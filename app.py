"""
Smart Attendance System — Professional Edition v5
NEW: Roll Number System + Per-Student Unique QR Codes
- Each student gets a QR with their roll number embedded
- Faculty enters roll number to generate student-specific QR
- Invalid/unregistered roll numbers produce invalid QR
- Proxy eliminated: QR is unique per-student per-session
"""

from flask import (Flask, render_template, request, redirect,
    session, send_file, jsonify)
import sqlite3, qrcode, time, os, re, io, threading, hashlib, hmac
import pandas as pd
from datetime import datetime, timedelta
import pytz, matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import bcrypt

from functools import wraps

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "smartattend_pro_v5_xK9mPqR")
app.permanent_session_lifetime = timedelta(hours=8)

# ── CONFIG ────────────────────────────────────────────────────────────────────
CAMPUS_LAT    = float(os.environ.get("CAMPUS_LAT",  "17.4065"))
CAMPUS_LNG    = float(os.environ.get("CAMPUS_LNG",  "78.4772"))
CAMPUS_RADIUS = float(os.environ.get("CAMPUS_RADIUS","500"))
GPS_ENABLED   = os.environ.get("GPS_ENABLED","true").lower() == "true"
PRESENT_BEFORE= int(os.environ.get("PRESENT_BEFORE","570"))   # 9:30
LATE_BEFORE   = int(os.environ.get("LATE_BEFORE",   "600"))   # 10:00
EMAIL_ENABLED = os.environ.get("EMAIL_ENABLED","false").lower() == "true"
EMAIL_SENDER  = os.environ.get("EMAIL_SENDER", "your_gmail@gmail.com")
EMAIL_PASSWORD= os.environ.get("EMAIL_PASSWORD","your_app_password")
EMAIL_HOST    = os.environ.get("EMAIL_HOST","smtp.gmail.com")
EMAIL_PORT    = int(os.environ.get("EMAIL_PORT","587"))
QR_INTERVAL   = int(os.environ.get("QR_INTERVAL","300")) # per-student QR lasts 60s
DB_PATH       = "attendance.db"

# ── ROLL NUMBER VALIDATION PATTERN ────────────────────────────────────────────
# Pattern: 2 digits + B + 2 digits + A + 4 alphanumeric chars (uppercase)
# Example valid: 24B81A3235, 23B81A0101
ROLL_PATTERN = re.compile(r"^[A-Za-z0-9]+$")

# Global session state — stores the ACTIVE session token for this class
# Per-student QR tokens stored in DB
session_lock   = threading.Lock()
session_state  = {"session_token": None, "started_at": 0, "active": False}

# ── DATABASE ──────────────────────────────────────────────────────────────────def get_db():
# ── DATABASE ─────────────────────────────────────────
def get_db():
    c = sqlite3.connect(DB_PATH, timeout=30, check_same_thread=False)
    c.row_factory = sqlite3.Row
    return c

def init_db():
    c = get_db()
    cur = c.cursor()

    cur.execute("""CREATE TABLE IF NOT EXISTS students(
        id           INTEGER PRIMARY KEY AUTOINCREMENT,
        roll_no      TEXT UNIQUE NOT NULL,
        email        TEXT UNIQUE NOT NULL,
        password     TEXT NOT NULL,
        name         TEXT DEFAULT ''
    )""")

    cur.execute("""CREATE TABLE IF NOT EXISTS faculty(
        id       INTEGER PRIMARY KEY AUTOINCREMENT,
        username TEXT UNIQUE NOT NULL,
        password TEXT NOT NULL
    )""")

    cur.execute("""CREATE TABLE IF NOT EXISTS attendance(
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        roll_no     TEXT NOT NULL,
        email       TEXT NOT NULL,
        name        TEXT DEFAULT '',
        marked_time TEXT NOT NULL,
        status      TEXT DEFAULT 'Present',
        latitude    REAL,
        longitude   REAL
    )""")

    # Table to track issued per-student QR tokens
    cur.execute("""CREATE TABLE IF NOT EXISTS qr_tokens(
        id          INTEGER PRIMARY KEY AUTOINCREMENT,
        roll_no     TEXT NOT NULL,
        token       TEXT NOT NULL UNIQUE,
        session_tok TEXT NOT NULL,
        issued_at   REAL NOT NULL,
        expires_at  REAL NOT NULL,
        used        INTEGER DEFAULT 0
    )""")

    cur.execute("""CREATE TABLE IF NOT EXISTS campus_config(
        id INTEGER PRIMARY KEY,
        lat REAL, lng REAL, radius REAL
    )""")

    if cur.execute("SELECT COUNT(*) FROM campus_config").fetchone()[0] == 0:
        cur.execute("INSERT INTO campus_config(id,lat,lng,radius) VALUES(1,?,?,?)",
                    (CAMPUS_LAT, CAMPUS_LNG, CAMPUS_RADIUS))

    c.commit()
    c.close()

    # Migrate old schema if needed
    for stmt in [
        "ALTER TABLE attendance ADD COLUMN roll_no TEXT DEFAULT ''",
        "ALTER TABLE attendance ADD COLUMN name TEXT DEFAULT ''",
        "ALTER TABLE attendance RENAME COLUMN time TO marked_time",
    ]:
        try:
            c2 = get_db(); c2.execute(stmt); c2.commit(); c2.close()
        except: pass

init_db()

# ── UTILS ─────────────────────────────────────────────────────────────────────
def hash_pw(p):  return bcrypt.hashpw(p.encode(), bcrypt.gensalt()).decode()
def check_pw(p, h):
    try:    return bcrypt.checkpw(p.encode(), h.encode())
    except: return p == h

def valid_pw(p):
    return (len(p) >= 6 and re.search(r"[a-z]", p)
            and re.search(r"\d", p) and re.search(r"[@#$%^&*]", p))

def valid_roll(roll):
    """Validate roll number format. Must be uppercase to match."""
    return bool(ROLL_PATTERN.match(roll.upper())) if roll else False

def normalize_roll(roll):
    return roll.strip().upper()

def get_status():
    ist  = pytz.timezone("Asia/Kolkata")
    now  = datetime.now(ist)
    mins = now.hour * 60 + now.minute
    return "Present" if mins < PRESENT_BEFORE else ("Late" if mins < LATE_BEFORE else "Absent")

def haversine(lat1, lng1, lat2, lng2):
    from math import radians, sin, cos, sqrt, atan2
    R = 6371000
    p1, p2 = radians(lat1), radians(lat2)
    a = sin((p2-p1)/2)**2 + cos(p1)*cos(p2)*sin(radians(lng2-lng1)/2)**2
    return R * 2 * atan2(sqrt(a), sqrt(1-a))

def send_email(to, subject, body):
    if not EMAIL_ENABLED: return
    try:
        import smtplib
        from email.mime.text import MIMEText
        from email.mime.multipart import MIMEMultipart
        msg = MIMEMultipart("alternative")
        msg["Subject"] = subject; msg["From"] = EMAIL_SENDER; msg["To"] = to
        msg.attach(MIMEText(body, "html"))
        with smtplib.SMTP(EMAIL_HOST, EMAIL_PORT) as s:
            s.starttls(); s.login(EMAIL_SENDER, EMAIL_PASSWORD)
            s.sendmail(EMAIL_SENDER, to, msg.as_string())
    except Exception as e: print(f"[Email] {e}")

def make_token(roll_no, session_tok):
    """Create a unique, unpredictable token for a student's QR."""
    raw = f"{roll_no}:{session_tok}:{time.time()}:{os.urandom(8).hex()}"
    return hashlib.sha256(raw.encode()).hexdigest()[:32]

def generate_session():
    """Faculty starts a new attendance session — issues a session token."""
    tok = os.urandom(16).hex()
    with session_lock:
        session_state["session_token"] = tok
        session_state["started_at"]    = time.time()
        session_state["active"]        = True
    return tok

def generate_student_qr(roll_no):
    """
    Generate a QR code unique to this student + current session.
    Returns (token, qr_filename) or (None, None) if roll invalid/not registered.
    """
    roll_no = normalize_roll(roll_no)

    # Validate roll number format
    if not valid_roll(roll_no):
        return None, None, "invalid_format"

    # Check if student is registered
    c = get_db()
    student = c.execute("SELECT * FROM students WHERE roll_no=?", (roll_no,)).fetchone()
    c.close()

    if not student:
        return None, None, "not_registered"

    with session_lock:
        if not session_state["active"]:
            return None, None, "no_session"
        sess_tok = session_state["session_token"]

    # Create unique token for this student
    token = make_token(roll_no, sess_tok)
    expires_at = time.time() + QR_INTERVAL

    # Store token in DB
    c = get_db()
    # Invalidate any previous tokens for this roll in this session
    c.execute("UPDATE qr_tokens SET used=2 WHERE roll_no=? AND session_tok=? AND used=0",
              (roll_no, sess_tok))
    c.execute(
        "INSERT INTO qr_tokens(roll_no,token,session_tok,issued_at,expires_at,used) VALUES(?,?,?,?,?,0)",
        (roll_no, token, sess_tok, time.time(), expires_at)
    )
    c.commit()
    c.close()

    # Build URL
    base_url = os.environ.get("BASE_URL", "https://smart-attendance-786f.onrender.com")
    url = f"{base_url}/mark_student/{token}"

    # Generate QR image
    os.makedirs("static/qr_codes", exist_ok=True)
    qr_path = f"static/qr_codes/{roll_no}.png"

    qr = qrcode.QRCode(version=1,
                       error_correction=qrcode.constants.ERROR_CORRECT_H,
                       box_size=8, border=2)
    qr.add_data(url)
    qr.make(fit=True)
    img = qr.make_image(fill_color="black", back_color="white")
    img.save(qr_path)

    return token, qr_path, "ok"

def faculty_required(f):
    @wraps(f)
    def w(*a, **k):
        if "faculty" not in session: return redirect("/faculty_login")
        return f(*a, **k)
    return w

def student_required(f):
    @wraps(f)
    def w(*a, **k):
        if "student" not in session: return redirect("/student_login")
        return f(*a, **k)
    return w

# ── ROUTES ────────────────────────────────────────────────────────────────────
@app.route("/")
def home(): return render_template("index.html")

# ── STUDENT AUTH ──────────────────────────────────────────────────────────────
@app.route("/signup", methods=["GET", "POST"])
def signup():
    if request.method == "POST":
        roll_no  = normalize_roll(request.form.get("roll_no", ""))
        email    = request.form["email"].strip().lower()
        password = request.form["password"]
        name     = request.form.get("name", "").strip()

        if not valid_roll(roll_no):
            return render_template("student_signup.html",
                error=f"Invalid roll number format: '{roll_no}'. Example: 24B81A3235")

        if not valid_pw(password):
            return render_template("student_signup.html",
                error="Password needs 6+ chars, lowercase, number, and special char (@ # $ % ^ & *).")

        try:
            c = get_db()
            c.execute("INSERT INTO students(roll_no,email,password,name) VALUES(?,?,?,?)",
                      (roll_no, email, hash_pw(password), name))
            c.commit()
            c.close()
            return redirect("/student_login")
        except sqlite3.IntegrityError as e:
            err_msg = "Roll number already registered." if "roll_no" in str(e) else "Email already registered."
            return render_template("student_signup.html", error=err_msg)
    return render_template("student_signup.html")

@app.route("/student_login", methods=["GET", "POST"])
def student_login():
    if request.method == "POST":
        identifier = request.form["identifier"].strip()   # Roll No or Email
        password   = request.form["password"]
        c = get_db()
        # Try roll number first, then email
        u = c.execute("SELECT * FROM students WHERE roll_no=? OR email=?",
                      (normalize_roll(identifier), identifier.lower())).fetchone()
        c.close()
        if u and check_pw(password, u["password"]):
            session.permanent = True
            session["student"]      = u["email"]
            session["roll_no"]      = u["roll_no"]
            session["student_name"] = u["name"] or u["roll_no"]
            return redirect("/student_dashboard")
        return render_template("student_login.html", error="Invalid roll number/email or password.")
    return render_template("student_login.html")

# ── FACULTY AUTH ──────────────────────────────────────────────────────────────
@app.route("/faculty_signup", methods=["GET", "POST"])
def faculty_signup():
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        password = request.form.get("password", "")

        if not valid_pw(password):
            return render_template("faculty_signup.html", error="Weak password")

        try:
            c = get_db()
            cur = c.cursor()

            cur.execute(
                "INSERT INTO faculty(username,password) VALUES(?,?)",
                (username, hash_pw(password))
            )

            c.commit()
            c.close()

            return redirect("/faculty_login")

        except sqlite3.IntegrityError:
            return render_template("faculty_signup.html", error="User already exists")

    return render_template("faculty_signup.html")

@app.route("/faculty_login", methods=["GET", "POST"])
def faculty_login():
    if request.method == "POST":
        
        c = get_db()
        u = c.execute("SELECT * FROM faculty WHERE username=?", (username,)).fetchone()
        c.close()
        if u and check_pw(password, u["password"]):
            session.permanent = True
            session["faculty"] = username
            generate_session()  # Start a new session on login
            return redirect("/faculty_dashboard")
        return render_template("faculty_login.html", error="Invalid credentials.")
    return render_template("faculty_login.html")

# ── FACULTY DASHBOARD ─────────────────────────────────────────────────────────
@app.route("/faculty_dashboard")
@faculty_required
def faculty_dashboard():
    ist   = pytz.timezone("Asia/Kolkata")
    today = datetime.now(ist).strftime("%Y-%m-%d")
    c     = get_db()
    total_stu      = c.execute("SELECT COUNT(*) FROM students").fetchone()[0]
    today_present  = c.execute("SELECT COUNT(*) FROM attendance WHERE DATE(marked_time)=? AND status='Present'", (today,)).fetchone()[0]
    today_late     = c.execute("SELECT COUNT(*) FROM attendance WHERE DATE(marked_time)=? AND status='Late'",    (today,)).fetchone()[0]
    total_records  = c.execute("SELECT COUNT(*) FROM attendance").fetchone()[0]
    campus         = c.execute("SELECT * FROM campus_config WHERE id=1").fetchone()
    c.close()
    pct = round((today_present / total_stu * 100) if total_stu > 0 else 0, 1)
    with session_lock:
        sess_active = session_state["active"]
        sess_tok    = session_state["session_token"]
    return render_template("faculty_dashboard.html",
        total_students=total_stu, today_present=today_present, today_late=today_late,
        attendance_pct=pct, total_records=total_records, campus=campus,
        gps_enabled=GPS_ENABLED, qr_interval=QR_INTERVAL,
        sess_active=sess_active,
        present_before=f"{PRESENT_BEFORE//60:02d}:{PRESENT_BEFORE%60:02d}",
        late_before=f"{LATE_BEFORE//60:02d}:{LATE_BEFORE%60:02d}")

# ── API: Generate QR for a specific roll number ───────────────────────────────
@app.route("/api/generate_qr", methods=["POST"])
@faculty_required
def api_generate_qr():
    data    = request.get_json()
    roll_no = data.get("roll_no", "").strip()

    token, qr_path, status = generate_student_qr(roll_no)

    if status == "invalid_format":
        return jsonify({"ok": False, "error": f"Invalid roll number format: '{roll_no}'. Expected format: 24B81A3235"})
    if status == "not_registered":
        return jsonify({"ok": False, "error": f"Roll number '{roll_no}' is not registered in the system."})
    if status == "no_session":
        return jsonify({"ok": False, "error": "No active session. Please refresh the dashboard."})

    roll_upper = normalize_roll(roll_no)
    c = get_db()
    student = c.execute("SELECT name, email FROM students WHERE roll_no=?", (roll_upper,)).fetchone()
    c.close()

    return jsonify({
        "ok": True,
        "roll_no": roll_upper,
        "student_name": student["name"] if student else roll_upper,
        "student_email": student["email"] if student else "",
        "qr_url": f"/static/qr_codes/{roll_upper}.png?t={int(time.time())}",
        "expires_in": QR_INTERVAL,
        "token": token
    })

# ── API: Start new session ────────────────────────────────────────────────────
@app.route("/api/new_session")
@faculty_required
def api_new_session():
    tok = generate_session()
    return jsonify({"ok": True, "session_token": tok})

# ── API: Chart data ───────────────────────────────────────────────────────────
@app.route("/api/chart_data")
@faculty_required
def api_chart_data():
    ist   = pytz.timezone("Asia/Kolkata")
    today = datetime.now(ist).date()
    c     = get_db()
    weekly = []
    for i in range(6, -1, -1):
        d = (today - timedelta(days=i)).strftime("%Y-%m-%d")
        p = c.execute("SELECT COUNT(*) FROM attendance WHERE DATE(marked_time)=? AND status='Present'", (d,)).fetchone()[0]
        l = c.execute("SELECT COUNT(*) FROM attendance WHERE DATE(marked_time)=? AND status='Late'",    (d,)).fetchone()[0]
        weekly.append({"date": d, "present": p, "late": l})
    students = c.execute(
        "SELECT roll_no, name, COUNT(*) as cnt FROM attendance GROUP BY roll_no ORDER BY cnt DESC LIMIT 10"
    ).fetchall()
    status_d = c.execute(
        "SELECT status, COUNT(*) as cnt FROM attendance WHERE DATE(marked_time)=? GROUP BY status",
        (today.strftime("%Y-%m-%d"),)).fetchall()
    c.close()
    return jsonify({
        "weekly": weekly,
        "students": [{"label": f"{r['roll_no']}", "count": r["cnt"]} for r in students],
        "status":   [{"label": r["status"], "count": r["cnt"]} for r in status_d],
    })

# ── STUDENT DASHBOARD ─────────────────────────────────────────────────────────
@app.route("/student_dashboard")
@student_required
def student_dashboard():
    email    = session["student"]
    roll_no  = session.get("roll_no", "")
    ist      = pytz.timezone("Asia/Kolkata")
    today    = datetime.now(ist).strftime("%Y-%m-%d")
    c        = get_db()
    total_days   = c.execute("SELECT COUNT(DISTINCT DATE(marked_time)) FROM attendance").fetchone()[0]
    my_p         = c.execute("SELECT COUNT(*) FROM attendance WHERE roll_no=? AND status='Present'", (roll_no,)).fetchone()[0]
    my_l         = c.execute("SELECT COUNT(*) FROM attendance WHERE roll_no=? AND status='Late'",    (roll_no,)).fetchone()[0]
    today_rec    = c.execute("SELECT status FROM attendance WHERE roll_no=? AND DATE(marked_time)=?", (roll_no, today)).fetchone()
    campus       = c.execute("SELECT * FROM campus_config WHERE id=1").fetchone()
    c.close()
    my_tot = my_p + my_l
    my_pct = round((my_tot / total_days * 100) if total_days > 0 else 0, 1)
    return render_template("student_dashboard.html",
        my_present=my_p, my_late=my_l, my_total=my_tot, my_pct=my_pct,
        today_marked=today_rec["status"] if today_rec else None,
        campus_lat=campus["lat"] if campus else CAMPUS_LAT,
        campus_lng=campus["lng"] if campus else CAMPUS_LNG,
        campus_radius=campus["radius"] if campus else CAMPUS_RADIUS,
        gps_enabled=GPS_ENABLED)

# ── MARK ATTENDANCE via student-specific QR token ─────────────────────────────
@app.route("/mark_student/<token>")
@student_required
def mark_student(token):
    email    = session["student"]
    roll_no  = session.get("roll_no", "")
    ist      = pytz.timezone("Asia/Kolkata")
    now      = datetime.now(ist)
    today    = now.strftime("%Y-%m-%d")
    ts       = now.strftime("%Y-%m-%d %H:%M:%S")

    c = get_db()

    # Validate token
    tok_row = c.execute(
        "SELECT * FROM qr_tokens WHERE token=?", (token,)
    ).fetchone()

    if not tok_row:
        c.close()
        return render_template("result.html",
            message="Invalid QR Code",
            color="red",
            sub="This QR code is not recognized. Make sure faculty generated it for your roll number.")

    if tok_row["used"] == 1:
        c.close()
        return render_template("result.html",
            message="QR Already Used",
            color="red",
            sub="This QR code has already been scanned. Each QR is single-use per student.")

    if time.time() > tok_row["expires_at"]:
        c.close()
        return render_template("result.html",
            message="QR Code Expired",
            color="red",
            sub=f"This QR expired. Ask faculty to generate a fresh QR for roll number {roll_no}.")

    # Verify this token was issued for THIS student's roll number
    if tok_row["roll_no"] != roll_no:
        c.close()
        return render_template("result.html",
            message="Wrong QR Code",
            color="red",
            sub=f"This QR was issued for roll number <strong>{tok_row['roll_no']}</strong>, but you are logged in as <strong>{roll_no}</strong>. Only scan the QR generated for your roll number.")

    # Check for duplicate today
    existing = c.execute(
        "SELECT * FROM attendance WHERE roll_no=? AND DATE(marked_time)=?",
        (roll_no, today)).fetchone()
    if existing:
        c.close()
        return render_template("result.html",
            message="Already Marked Today",
            color="orange",
            sub=f"Your attendance was already recorded as <strong>{existing['status']}</strong> today.")

    # GPS check
    lat = request.args.get("lat", type=float)
    lng = request.args.get("lng", type=float)
    if GPS_ENABLED and lat is not None and lng is not None:
        campus = c.execute("SELECT * FROM campus_config WHERE id=1").fetchone()
        dist   = haversine(lat, lng, campus["lat"], campus["lng"])
        if dist > campus["radius"]:
            c.close()
            return render_template("result.html",
                message="Outside Campus Boundary",
                color="red",
                sub=f"You are {int(dist)}m from campus. Must be within {int(campus['radius'])}m.")

    status = get_status()

    # Get student info
    student = c.execute("SELECT * FROM students WHERE roll_no=?", (roll_no,)).fetchone()
    name    = student["name"] if student else ""

    # Mark attendance
    c.execute(
        "INSERT INTO attendance(roll_no,email,name,marked_time,status,latitude,longitude) VALUES(?,?,?,?,?,?,?)",
        (roll_no, email, name, ts, status, lat, lng))

    # Mark token as used
    c.execute("UPDATE qr_tokens SET used=1 WHERE token=?", (token,))
    c.commit()
    c.close()

    send_email(email, "✅ SmartAttend — Attendance Confirmed",
        f"<p>Roll No: <b>{roll_no}</b><br>Name: <b>{name}</b><br>Time: <b>{ts}</b> IST<br>Status: <b>{status}</b></p>")

    color = "green" if status == "Present" else "orange"
    return render_template("result.html",
        message=f"Attendance Marked — {status}",
        color=color,
        sub=f"Roll: {roll_no} | {ts} IST")

# ── GPS CHECK ─────────────────────────────────────────────────────────────────
@app.route("/api/check_location", methods=["POST"])
@student_required
def api_check_location():
    data   = request.get_json()
    lat    = data.get("lat"); lng = data.get("lng")
    if not GPS_ENABLED: return jsonify({"ok": True, "message": "GPS disabled"})
    if lat is None or lng is None: return jsonify({"ok": False, "message": "Location unavailable"})
    c      = get_db()
    campus = c.execute("SELECT * FROM campus_config WHERE id=1").fetchone()
    c.close()
    dist   = haversine(lat, lng, campus["lat"], campus["lng"])
    ok     = dist <= campus["radius"]
    return jsonify({"ok": ok, "distance": int(dist), "radius": int(campus["radius"]),
                    "message": f"{int(dist)}m from campus (limit {int(campus['radius'])}m)"})

# ── REPORT ────────────────────────────────────────────────────────────────────
@app.route("/report", methods=["GET", "POST"])
@faculty_required
def report():
    ist      = pytz.timezone("Asia/Kolkata")
    today    = datetime.now(ist).strftime("%Y-%m-%d")
    selected = request.form.get("date", today) if request.method == "POST" else request.args.get("date", today)
    mode     = request.args.get("mode", "daily")
    c        = get_db()
    if mode == "weekly":
        d_from = (datetime.now(ist) - timedelta(days=6)).strftime("%Y-%m-%d")
        rows   = c.execute(
            "SELECT * FROM attendance WHERE DATE(marked_time) BETWEEN ? AND ? ORDER BY marked_time DESC",
            (d_from, today)).fetchall()
        label  = f"{d_from} → {today}"
    else:
        rows   = c.execute(
            "SELECT * FROM attendance WHERE DATE(marked_time)=? ORDER BY roll_no ASC",
            (selected,)).fetchall()
        label  = selected
    total_stu = c.execute("SELECT COUNT(*) FROM students").fetchone()[0]
    c.close()
    data = [(r["id"], r["roll_no"], r["name"], r["email"], r["marked_time"], r["status"]) for r in rows]
    p_ct = sum(1 for r in data if r[5] == "Present")
    l_ct = sum(1 for r in data if r[5] == "Late")
    pct  = round((p_ct / total_stu * 100) if total_stu > 0 else 0, 1)
    return render_template("report.html",
        data=data, selected_date=selected, selected_label=label,
        present_ct=p_ct, late_ct=l_ct, total_students=total_stu,
        pct=pct, view_mode=mode)

# ── GRAPH ─────────────────────────────────────────────────────────────────────
@app.route("/graph")
@faculty_required
def graph():
    c    = get_db()
    rows = c.execute("SELECT roll_no, name, COUNT(*) as cnt FROM attendance GROUP BY roll_no ORDER BY cnt DESC").fetchall()
    c.close()
    labels = [f"{r['roll_no']}" for r in rows]
    counts = [r["cnt"] for r in rows]
    plt.style.use("dark_background")
    fig, ax = plt.subplots(figsize=(max(10, len(labels)*1.2), 6))
    colors  = ["#0ea5e9","#10b981","#f59e0b","#8b5cf6","#ef4444","#06b6d4","#84cc16","#f97316","#ec4899"]
    bars    = ax.bar(labels, counts, color=[colors[i % len(colors)] for i in range(len(labels))], width=0.55)
    for bar, cnt in zip(bars, counts):
        ax.text(bar.get_x()+bar.get_width()/2, bar.get_height()+.08, str(cnt),
                ha='center', va='bottom', fontsize=10, color='white', fontweight='bold')
    ax.set_xlabel("Roll Number", fontsize=11, labelpad=8)
    ax.set_ylabel("Total Attendance Days", fontsize=11, labelpad=8)
    ax.set_title("Student Attendance Analytics — By Roll Number", fontsize=13, fontweight='bold', pad=14)
    ax.set_facecolor("#0b1628"); fig.patch.set_facecolor("#0b1628")
    ax.tick_params(axis='x', rotation=30, colors='#7a9bbf', labelsize=8)
    ax.tick_params(axis='y', colors='#7a9bbf')
    for sp in ['top','right']: ax.spines[sp].set_visible(False)
    for sp in ['bottom','left']: ax.spines[sp].set_color('#1a2d48')
    ax.yaxis.set_major_locator(plt.MaxNLocator(integer=True))
    if not labels:
        ax.text(0.5, 0.5, 'No attendance data yet', transform=ax.transAxes,
                ha='center', va='center', fontsize=13, color='#3d5a7a')
    plt.tight_layout()
    os.makedirs("static", exist_ok=True)
    plt.savefig("static/graph.png", dpi=120)
    plt.close(fig)
    return render_template("graph.html")

# ── EXPORT EXCEL ──────────────────────────────────────────────────────────────
@app.route("/export")
@faculty_required
def export_excel():
    c    = get_db()
    rows = c.execute("SELECT * FROM attendance ORDER BY marked_time DESC").fetchall()
    c.close()
    data = [(r["id"], r["roll_no"], r["name"], r["email"], r["marked_time"], r["status"],
             r["latitude"], r["longitude"]) for r in rows]
    df   = pd.DataFrame(data, columns=["ID","Roll No","Name","Email","Timestamp (IST)","Status","Latitude","Longitude"])
    path = "attendance_export.xlsx"
    df.to_excel(path, index=False)
    return send_file(path, as_attachment=True)

# ── EXPORT PDF ────────────────────────────────────────────────────────────────
@app.route("/export_pdf")
@faculty_required
def export_pdf():
    try:
        from reportlab.lib.pagesizes import A4
        from reportlab.lib import colors as rl_c
        from reportlab.lib.styles import getSampleStyleSheet
        from reportlab.platypus import SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer
    except ImportError:
        return "reportlab not installed. Run: pip install reportlab", 500
    ist   = pytz.timezone("Asia/Kolkata")
    today = datetime.now(ist).strftime("%Y-%m-%d")
    date  = request.args.get("date", today)
    c     = get_db()
    rows  = c.execute("SELECT * FROM attendance WHERE DATE(marked_time)=? ORDER BY roll_no ASC", (date,)).fetchall()
    total = c.execute("SELECT COUNT(*) FROM students").fetchone()[0]
    c.close()
    buf   = io.BytesIO()
    doc   = SimpleDocTemplate(buf, pagesize=A4, topMargin=36, bottomMargin=36, leftMargin=48, rightMargin=48)
    S     = getSampleStyleSheet(); story = []
    story.append(Paragraph("Smart Attendance System — Professional", S["Title"]))
    story.append(Paragraph(f"Daily Report: {date}", S["Normal"])); story.append(Spacer(1, 10))
    p_ct = sum(1 for r in rows if r["status"]=="Present")
    l_ct = sum(1 for r in rows if r["status"]=="Late")
    pct  = round((p_ct/total*100) if total>0 else 0, 1)
    story.append(Paragraph(f"Present: {p_ct}  |  Late: {l_ct}  |  Total Students: {total}  |  Rate: {pct}%", S["Normal"]))
    story.append(Spacer(1, 14))
    td = [["#","Roll No","Name","Email","Time (IST)","Status"]]
    for i, r in enumerate(rows, 1):
        td.append([str(i), r["roll_no"], r["name"] or "—", r["email"], r["marked_time"], r["status"]])
    tbl = Table(td, colWidths=[22, 72, 80, 150, 110, 54])
    tbl.setStyle(TableStyle([
        ("BACKGROUND", (0,0),(-1,0), rl_c.HexColor("#0ea5e9")),
        ("TEXTCOLOR",  (0,0),(-1,0), rl_c.white),
        ("FONTNAME",   (0,0),(-1,0), "Helvetica-Bold"),
        ("FONTSIZE",   (0,0),(-1,-1), 8),
        ("ROWBACKGROUNDS",(0,1),(-1,-1),[rl_c.white,rl_c.HexColor("#f0f9ff")]),
        ("GRID",       (0,0),(-1,-1), 0.35, rl_c.HexColor("#cbd5e1")),
        ("TOPPADDING", (0,0),(-1,-1), 5),("BOTTOMPADDING",(0,0),(-1,-1),5),
        ("LEFTPADDING",(0,0),(-1,-1), 6),
    ]))
    story.append(tbl); doc.build(story); buf.seek(0)
    return send_file(buf, as_attachment=True,
                     download_name=f"attendance_{date}.pdf",
                     mimetype="application/pdf")

# ── CAMPUS CONFIG ─────────────────────────────────────────────────────────────
@app.route("/campus_config", methods=["GET","POST"])
@faculty_required
def campus_config():
    c      = get_db()
    campus = c.execute("SELECT * FROM campus_config WHERE id=1").fetchone()
    if request.method == "POST":
        c.execute("UPDATE campus_config SET lat=?,lng=?,radius=? WHERE id=1",
                  (float(request.form["lat"]), float(request.form["lng"]), float(request.form["radius"])))
        c.commit(); c.close()
        return redirect("/faculty_dashboard")
    c.close()
    return render_template("campus_config.html", campus=campus)

# ── STUDENT LIST ──────────────────────────────────────────────────────────────
@app.route("/students")
@faculty_required
def students():
    c    = get_db()
    rows = c.execute("SELECT * FROM students ORDER BY roll_no ASC").fetchall()
    c.close()
    return render_template("students.html", students=rows)

# ── LOGOUT ────────────────────────────────────────────────────────────────────
@app.route("/logout")
def logout():
    session.clear()
    return redirect("/")

from waitress import serve

if __name__ == "__main__":
    print("Starting server...")
    serve(app, host="127.0.0.1", port=5000)
