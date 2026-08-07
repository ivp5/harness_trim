#!/usr/bin/env python3
"""TRIM — LLM harness store trim only (Cursor / Codex / Claude).

Works on bloated agent sessions / jsonl for all three harnesses:
  Cursor  — ~/.cursor/chats/*/store.db (protobuf blob graph; cut/settle)
  Codex   — ~/.codex/sessions/**/rollout-*.jsonl (bloated transcript jsonl)
  Claude  — ~/.claude/projects/**/*.jsonl (bloated session jsonl)
plus harness clutter (agent-tools, tracking, Claude file-history tip-keep).

Two organs, never fused:
  cut/settle  — rewrite live store; leave undo sibling beside it
  retire      — ONLY removal: shutil.move → ~/.Trash

Generality over kludge:
  KIND    — scan/enrich/cut/verify drivers (register a kind; no if-ladder owner)
  PATCHES — seed roots; free always tip-keeps (no broom zoo)
  UNDO    — one marker table; cut mints names that match it

Undo siblings are never auto-retired. Disk-free is not a goal of cut.
"""
from __future__ import annotations
import argparse, hashlib, json, os, re, resource, shutil, signal, sqlite3, subprocess, sys, tempfile, threading, time, traceback, uuid
from collections import Counter, defaultdict, deque, namedtuple
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from enum import Enum, IntFlag, auto
from pathlib import Path

Ref = namedtuple("Ref", "id law tag")
View = namedtuple("View", "turns always headers maps unknown")

HOME = Path.home()
TRASH = HOME / ".Trash"
CURSOR_HOME = HOME / ".cursor"
CURSOR_CHATS = CURSOR_HOME / "chats"
CURSOR_PROJS = CURSOR_HOME / "projects"
CURSOR_TRACKING = CURSOR_HOME / "ai-tracking" / "ai-code-tracking.db"
CODEX_HOME = HOME / ".codex"
CODEX_SESS = CODEX_HOME / "sessions"
CLAUDE_HOME = HOME / ".claude"
CLAUDE_PROJS = CLAUDE_HOME / "projects"
REACH_NAME = "store.db.reachable"
REACH_META_NAME = "store.db.reachable.meta.json"
SETTLED_NAME = "store.db.settled.json"
SIBLING_GLOBS = (
    "store.db.bak*", "store.db.bloated*", "store.db.pretrim*",
    "store.db.prerestore*", "store.db.*.quarantined*", "store.db.ultraslim*",
    "store.db.new-*", "store.db.failed-*",
)
UNDO_PREFIXES = ("store.db.bloated", "store.db.prerestore")
UNDO_SUBSTR = (".pretrim",)
KINDS = ("cursor", "codex", "claude")
MAX_LEAF, DEFAULT_RECENT, MIN_TURNS = 256 * 1024, 80, 10
MAX_BLOBS, MAX_BYTES, MIN_BLOBS = 20000, 250_000_000, 100
DEFAULT_TOOL_CAP = 2048
# cut levels: recent turns kept. Default is the safest (keeps most history).
CUT_LEVELS = {
    "safe":   160,  # default — keep more turns
    "normal": 80,
    "tight":  40,
}
CUT_DEFAULT = "safe"

# --- retire organ (sole removal) + undo fence (cut must not reclaim) ---
def is_cut_undo(p: Path) -> bool:
    """Undo left by cut — never auto-retired. UNDO_* tables only."""
    n = Path(p).name
    if any(n.startswith(pfx) for pfx in UNDO_PREFIXES):
        return True
    return any(s in n for s in UNDO_SUBSTR)

def _trash_dest(name: str) -> Path:
    TRASH.mkdir(exist_ok=True)
    dest = TRASH / name
    if not dest.exists() and not dest.is_symlink():
        return dest
    ts = time.strftime("%Y%m%dT%H%M%S")
    dest = TRASH / f"{name}.{ts}.{os.getpid()}"
    n = 0
    while dest.exists() or dest.is_symlink():
        n += 1
        dest = TRASH / f"{name}.{ts}.{os.getpid()}.{n}"
    return dest

def retire(p: Path, *, undo_ok: bool = False) -> int:
    """Move path to macOS Trash. Sole removal primitive. Refuses cut-undo unless undo_ok."""
    p = Path(p)
    if not p.exists() and not p.is_symlink():
        return 0
    if not undo_ok and is_cut_undo(p):
        INSTR["retire_undo_refused"] += 1
        return 0
    try:
        if p.is_dir() and not p.is_symlink():
            sz = _du_bytes(p, fresh=True)
        else:
            sz = p.stat().st_size
    except OSError:
        sz = 0
    dest = _trash_dest(p.name)
    parent = p.parent
    shutil.move(str(p), str(dest))
    _du_bust_lineage(parent, p)
    return sz

INSTR = Counter()
_DU_CACHE: dict = {}
_DU_DISK_LOADED = False
_DU_DISK_DIRTY = False
_DU_LOCK = threading.Lock()

_MASS_CACHE: dict = {}
_MASS_DISK_LOADED = False
_MASS_DISK_DIRTY = False
_MASS_LOCK = threading.Lock()
_MASS_COMPACT_KEYS = (
    "file_mb", "payload_mb", "n_blobs", "graph_mb", "out_of_graph_mb",
    "plan_keep_mb", "admit_drop_mb", "turns", "n_graph", "skip", "admit_buckets",
)

_LSOF_CACHE: dict = {}
_LSOF_BY: dict = defaultdict(list)
_LSOF_PROBES: list = []
_LSOF_OWNER: list = []
_LSOF_CUR_PID = None
LSOF_UNKNOWN: set = set()  # paths whose last lsof timed out / errored — not cached as free
LSOF_UNKNOWN_PID = -1  # sentinel so bool(lock_pids) / held.get is truthy (= refuse)
_LOCK_SNAP = None
HOLD_PROBES: list = []

_TURNS: list = []
_ALWAYS: list = []
_HEADERS: list = []
_MAPS: list = []
_UNKNOWN: list = []
_REFS: list = []
_EDGE: list = []
_EDGE_SEEN: set = set()
_RECENT_SET: set = set()

PLAN_ROOT = ""
PLAN_AGENT = None
PLAN_META_ROWS: list = []
PLAN_KEEP: dict = {}
PLAN_DROP: dict = {}
PLAN_MISSING: list = []
PLAN_TURNS: list = []
PLAN_RECENT: list = []
PLAN_BYTES = 0

_SNAP_BLOB_A: dict = {}
_SNAP_LN_A: dict = {}
_SNAP_BLOB_B: dict = {}
_SNAP_LN_B: dict = {}
_SNAP_SLOT = 0

GRAPH_ORDER: list = []
GRAPH_QUEUED: set = set()
GRAPH_HEAD = 0
GRAPH_BYTES = 0
GRAPH_TAG: dict = {}
GRAPH_TERMINAL_TAGS = frozenset({"root:f1", "root:f4"})
GRAPH_STEP_EXPAND_MAX = 64
GRAPH_F3_EXPAND_MAX = 80

MAT_ROWS: list = []
SIB_PATHS: dict = {}
MASS: dict = {}
SESSIONS: list = []
PRESSURE_FAILS = 0
_MAP_POOL = None
_CWD_IDX = None
_CWD_IDX_FP = None
LSOF_PROBE_FP: list = []
STORE_IDX: dict = {}
STORE_WIN: dict = {}
SIB_WIN: dict = {}
TX_IDX: dict = {}
TX_WIN = None
HOLD_PROBE_WIN: dict = {}
HARVEST_CLAIMED_READY = False
PB_VARINT_BUF = bytearray()
PHASE: dict = {}
CHECK_FAILS: list = []
CHECK_INFO: dict = {}

TEXT_PARTS: list = []
LSOF_OUT: dict = {}
LSOF_RESULT: dict = {}
LSOF_SEEN: dict = {}
LSOF_FMAP: dict = {}
SMOKE_ERR: list = []
SMOKE_REP: dict = {}
FALSIFY_ALARMS: list = []
FALSIFY_INFO: dict = {}
FALSIFY_REP: dict = {}
CAP_OUT: list = []
CODEX_KEEP = bytearray()
CODEX_STATS: dict = {}
CODEX_RH: list = []
CODEX_ALIGN_LINES: list = []
CODEX_ALIGN_SEEN: set = set()
CODEX_ALIGN_KEPT: list = []
CODEX_HEAD: list = []
SETTLE_ACTIONS: list = []
SETTLE_LEDGER: dict = {}
SETTLE_ALL_CHATS: list = []
SETTLE_ALL_OUT: list = []
META_SCRATCH: dict = {}
EXC_ENTRY: dict = {}
HARVEST_CLAIMED: set = set()
HARVEST_LOOSE: list = []
MAP_JOBS: list = []
MAP_SIZED: list = []
MAP_ROWS: list = []
CLAUDE_RECS: list = []
TRIPWIRE_REP: dict = {}
KIND: dict = {}
FREE_HB_EVERY = 5.0
_FREE_T0 = 0.0
_FREE_LAST = 0.0
_FREE_STOP = False
_FREE_SIG_PREV = None
_FREE_RUNNING = False
_FREE_PHASE = ""
_FREE_HB_LOCK = threading.Lock()

EXC_SIDECAR_CAP = 16
ENRICH_SKIP_CAP = 32
COARSE_BUCKETS: Counter = Counter()
ADMIT_BUCKETS: Counter = Counter()
EXC_SIDECAR: deque = deque(maxlen=EXC_SIDECAR_CAP)
LAST_EXC: dict = {}
ENRICH_SKIPS: deque = deque(maxlen=ENRICH_SKIP_CAP)
TRIPWIRE_HITS: Counter = Counter()
EvidenceLoss = namedtuple("EvidenceLoss", "compressed_into dropped_detail unfalsifiable_claim")
UNFALSIFIABLE_LEDGER = (
    EvidenceLoss("admit_drop_mb", "PLAN_DROP reason histogram", "tag/law class of tip admit_drop bytes"),
    EvidenceLoss("skip=plan:Exc", "exception site + traceback", "store_mass skip root cause"),
    EvidenceLoss("enrich_json_skip", "ENRICH_SKIPS off/n/err", "corrupt JSONL vs empty last_user"),
    EvidenceLoss("codex ui/world_state counts", "event payload bodies", "resume-critical world_state"),
    EvidenceLoss("codex tool_cap elision", "tool output middle", "tool failure string on later turn"),
    EvidenceLoss("claude thinking/tool drop", "thinking/tool bodies", "wrong tool-path reasoning"),
    EvidenceLoss("reach discard after install", "reach blob graph", "pre-install admit_drop mix"),
    EvidenceLoss("session summary compaction", "tool outputs + contacts", "pre-summary tip MB split"),
    EvidenceLoss("trim_slim dropped_surface", "falsify/mechanics/paths CLI", "living falsifier surfaces"),
    EvidenceLoss("dead_mb slogan", "none — split restored", "graph/out_of_graph/admit_drop"),
)

Allow = namedtuple("Allow", "prep isolate swap all")
PHASE_ALLOW = {
    (1, "STALE"):   Allow(prep=False, isolate=True,  swap=False, all=False),
    (1, "REACH"):   Allow(prep=False, isolate=True,  swap=False, all=False),
    (1, "SETTLED"): Allow(prep=False, isolate=True,  swap=False, all=False),
    (0, "STALE"):   Allow(prep=True,  isolate=True,  swap=False, all=True),
    (0, "REACH"):   Allow(prep=True,  isolate=True,  swap=True,  all=True),
    (0, "SETTLED"): Allow(prep=False, isolate=True,  swap=False, all=True),
}

PRODUCT_DIR_NAMES = frozenset({
    "chats", "sessions", "projects", "agent-transcripts", "ai-tracking",
})
StoreFingerprint = namedtuple("StoreFingerprint", "root mtime_ns size")
ROOT_LAW = {
    1: "MUST", 3: "MUST", 6: "MUST", 7: "MUST", 8: "MUST",
    11: "SEAL", 13: "SEAL", 12: "MAP", 31: "MAP",
}

def bump_coarse(bucket: str, n: int = 1) -> None:
    COARSE_BUCKETS[bucket] += n

def record_exception(site: str, e: BaseException) -> str:
    global LAST_EXC
    tb = "".join(traceback.format_exception(type(e), e, e.__traceback__))
    if len(tb) > 1200:
        tb = tb[-1200:]
    EXC_ENTRY.clear()
    EXC_ENTRY.update(site=site, typ=type(e).__name__, msg=str(e)[:300], tb=tb)
    EXC_SIDECAR.append(dict(EXC_ENTRY))
    LAST_EXC.clear(); LAST_EXC.update(EXC_ENTRY)
    bump_coarse(f"exc:{site}:{type(e).__name__}")
    return f"{site}:{type(e).__name__}:{str(e)[:80]}"

ADMIT_REASON_CLASS = (
    ("old_turn", "old_turn"),
    ("recent_large", "recent_large"),
    ("probe_large", "probe_large"),
)

def recount_admit_buckets() -> None:
    ADMIT_BUCKETS.clear()
    for reason in PLAN_DROP.values():
        cls = "other"
        for tok, name in ADMIT_REASON_CLASS:
            if tok in reason:
                cls = name
                break
        ADMIT_BUCKETS[cls] += 1
        ADMIT_BUCKETS[f"tag:{reason.split(':', 1)[0]}"] += 1

def coarse_report() -> dict:
    return dict(
        admit_buckets=dict(ADMIT_BUCKETS),
        coarse_buckets=dict(COARSE_BUCKETS),
        exc_sidecar_n=len(EXC_SIDECAR),
        last_exc=dict(LAST_EXC) if LAST_EXC else None,
        unfalsifiable=[row._asdict() for row in UNFALSIFIABLE_LEDGER],
    )

def _cursor_agent_dir() -> Path:
    env = os.environ.get("CURSOR_AGENT_DIR")
    if env:
        return Path(env)
    root = HOME / ".local/share/cursor-agent/versions"
    if root.is_dir():
        kids = [p for p in root.iterdir() if p.is_dir()]
        if kids:
            return max(kids, key=lambda p: p.stat().st_mtime)
    return root

AG = _cursor_agent_dir()

class PatchGuard(IntFlag):
    OPEN = 0
    OPT_IN = auto()

PATCH_GUARD_KNOWN = PatchGuard.OPEN | PatchGuard.OPT_IN

@dataclass(frozen=True)
class Patch:
    """Harness cache root. Free always tip-keeps — broom enum deleted."""
    name: str
    roots: tuple
    guard: PatchGuard = PatchGuard.OPEN
    note: str = ""

# Add a root → tip-keep emerges. No broom column to predict strategy.
_SEED = """
claude-file-history|.claude/file-history|0
"""

HARNESS_ROOTS = (
    CURSOR_CHATS, CURSOR_PROJS, CURSOR_TRACKING.parent,
    CODEX_SESS, CLAUDE_PROJS, CLAUDE_HOME / "file-history",
)

PATCHES: dict[str, Patch] = {}
for _line in _SEED.strip().splitlines():
    _parts = _line.split("|")
    _n, _rel, _o = _parts[0], _parts[1], _parts[-1]
    _root = HOME.joinpath(*_rel.split("/"))
    _bits = PatchGuard(int(_o))
    if int(_bits) & ~int(PATCH_GUARD_KNOWN):
        TRIPWIRE_HITS["T5_unknown_patch_guard_bits"] += 1
    _prev = PATCHES.get(_n)
    if _prev is None:
        PATCHES[_n] = Patch(_n, (_root,), _bits)
    else:
        PATCHES[_n] = Patch(_n, _prev.roots + (_root,), _prev.guard | _bits)

def default_reclaim_names() -> list[str]:
    return [n for n, p in PATCHES.items() if not (p.guard & PatchGuard.OPT_IN)]

def tripwire_hit(tid: str, n: int = 1) -> None:
    TRIPWIRE_HITS[tid] += n

def graph_walk_corrupt() -> bool:
    """Length/head O(1); same-length membership O(n) — no set(order) alloc."""
    n = len(GRAPH_ORDER)
    if not (0 <= GRAPH_HEAD <= n):
        return True
    if n != len(GRAPH_QUEUED):
        return True
    for hid in GRAPH_ORDER:
        if hid not in GRAPH_QUEUED:
            return True
    return False

def evaluate_tripwires() -> dict:
    unknown = [p.name for p in PATCHES.values()
               if int(p.guard) & ~int(PATCH_GUARD_KNOWN)]
    TRIPWIRE_REP.clear()
    rows = [
        dict(id="T4_graph_walk_corrupt",
             fired=graph_walk_corrupt(),
             detail=f"head={GRAPH_HEAD} order={len(GRAPH_ORDER)} queued={len(GRAPH_QUEUED)}"),
        dict(id="T5_unknown_patch_guard_bits",
             fired=bool(unknown) or TRIPWIRE_HITS["T5_unknown_patch_guard_bits"] > 0,
             detail=",".join(unknown) or f"hits={TRIPWIRE_HITS['T5_unknown_patch_guard_bits']}"),
        dict(id="T6_kind_registry",
             fired=set(KIND) != set(KINDS),
             detail=f"kind={sorted(KIND)} expect={list(KINDS)}"),
    ]
    TRIPWIRE_REP.update(tripwires=rows, any_fired=any(r["fired"] for r in rows))
    return TRIPWIRE_REP

@dataclass(frozen=True)
class Cut:
    recent: int = 40
    keep_mb: float = 25.0
    turns: int = 60
    tools: bool = True
    thinking: bool = False
    reasoning: bool = False
    tool_cap: int = DEFAULT_TOOL_CAP

    def with_(self, **kw):
        d = {f: getattr(self, f) for f in self.__dataclass_fields__}
        d.update(kw)
        return Cut(**d)

    def __str__(self):
        return (f"r{self.recent}/m{self.keep_mb}/t{self.turns} "
                f"tools={self.tools}@{self.tool_cap} R={self.reasoning} T={self.thinking}")

_BIRTH = Cut(tools=False, thinking=False, reasoning=False, tool_cap=DEFAULT_TOOL_CAP)

PRESETS: dict[str, Cut] = {
    "light":  _BIRTH.with_(recent=80, keep_mb=80, turns=120),
    "medium": _BIRTH.with_(recent=40, keep_mb=25, turns=60, tools=True),
    "heavy":  _BIRTH.with_(recent=20, keep_mb=8, turns=30, tools=True,
                           thinking=True, reasoning=True, tool_cap=512),
}

CODEX_UI_TYPES = frozenset({
    # Earned on live ~/.codex/sessions (4794 jsonl): drop types never observed.
    "token_count", "agent_message", "agent_reasoning",
    "patch_apply_end", "context_compacted",
})
_JSON_TYPE_RE = re.compile(br'"type"\s*:\s*"([^"]+)"')

CLAUDE_DROP_TYPES = {
    "file-history-snapshot", "file-history-delta", "last-prompt", "ai-title",
    "custom-title", "progress", "queue-operation", "attachment",
}

CLAUDE_PREAMBLE = {
    "mode", "permission-mode", "file-history-snapshot", "attachment", "system",
    "agent-name", "agent-setting",
}

class L(Enum):
    MUST, SEAL, RS, PROBE = auto(), auto(), auto(), auto()

class SkipChat(Exception):
    def __init__(self, why: str):
        super().__init__(why)
        self.why = why

def die(msg: str, code: int = 2) -> None:
    print(f"REFUSE: {msg}", file=sys.stderr); sys.exit(code)

def free_begin(label: str) -> None:
    """Arm 5s heartbeats + cooperative Ctrl-C for free/reclaim."""
    global _FREE_T0, _FREE_LAST, _FREE_STOP, _FREE_SIG_PREV
    global _FREE_RUNNING, _FREE_PHASE
    _FREE_T0 = _FREE_LAST = time.time()
    _FREE_STOP = False
    _FREE_PHASE = "start"
    _FREE_RUNNING = True
    print(label, flush=True)
    print("  Ctrl-C stops safely — already-Trashed files stay; no permanent delete",
          flush=True)
    def _on_sigint(_sig, _frame):
        global _FREE_STOP
        _FREE_STOP = True
        print("\n  Ctrl-C — stopping after current file…", flush=True)
    _FREE_SIG_PREV = signal.signal(signal.SIGINT, _on_sigint)
    def _ticker():
        # Covers long lsof/du subprocesses where the main thread cannot pulse.
        while True:
            time.sleep(FREE_HB_EVERY)
            with _FREE_HB_LOCK:
                if not _FREE_RUNNING:
                    return
                if _FREE_STOP:
                    return
                now = time.time()
                if (now - _FREE_LAST) < (FREE_HB_EVERY - 0.25):
                    continue
                _FREE_LAST = now
                phase = _FREE_PHASE or "working"
                print(f"  HEARTBEAT +{now - _FREE_T0:.0f}s  {phase}  (still working)",
                      flush=True)
    threading.Thread(target=_ticker, name="free-hb", daemon=True).start()

def free_pulse(phase: str, **kv) -> None:
    """Minimal status ≥ every FREE_HB_EVERY seconds. Raises KeyboardInterrupt if stopped."""
    global _FREE_LAST, _FREE_PHASE
    if _FREE_STOP:
        raise KeyboardInterrupt("free stop")
    now = time.time()
    force = kv.pop("_force", False)
    with _FREE_HB_LOCK:
        _FREE_PHASE = phase
        if not force and (now - _FREE_LAST) < FREE_HB_EVERY:
            return
        _FREE_LAST = now
    bits = " ".join(f"{k}={v}" for k, v in kv.items())
    print(f"  HEARTBEAT +{now - _FREE_T0:.0f}s  {phase}"
          + (f"  {bits}" if bits else ""), flush=True)

def free_end() -> None:
    global _FREE_SIG_PREV, _FREE_RUNNING
    _FREE_RUNNING = False
    if _FREE_SIG_PREV is not None:
        signal.signal(signal.SIGINT, _FREE_SIG_PREV)
        _FREE_SIG_PREV = None

def shasum(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for c in iter(lambda: f.read(1 << 20), b""): h.update(c)
    return h.hexdigest()

def open_ro(p: Path) -> sqlite3.Connection:
    uri = f"file:{p}?mode=ro"
    try:
        c = sqlite3.connect(uri, uri=True, timeout=5)
        c.execute("PRAGMA query_only=ON")
        c.execute("SELECT 1 FROM sqlite_master LIMIT 1")
        return c
    except sqlite3.Error:
        # immutable ignores WAL — may be a frozen/stale view of a busy DB
        INSTR["sqlite_immutable_fallback"] += 1
        c = sqlite3.connect(f"file:{p}?mode=ro&immutable=1", uri=True, timeout=5)
        c.execute("PRAGMA query_only=ON")
        return c

def _hold_probe_fp(p: Path) -> tuple:
    try:
        st = p.stat()
        base = (st.st_mtime_ns, st.st_ino, int(p.is_dir()))
    except OSError:
        return ()
    if not p.is_dir():
        return base
    parts = []
    for name in ("store.db", "store.db-wal", "store.db-shm"):
        q = p / name
        try:
            s = q.stat()
            parts.append((name, s.st_mtime_ns, s.st_ino, s.st_size))
        except OSError:
            parts.append((name, 0, 0, 0))
    return base + (tuple(parts),)

def hold_probes(p: Path) -> list[Path]:
    HOLD_PROBES.clear()
    wkey = _du_key(p)
    fp = _hold_probe_fp(p)
    hit = HOLD_PROBE_WIN.get(wkey)
    if hit is not None and hit[0] == fp:
        INSTR["hold_probe_hit"] += 1
        HOLD_PROBES.extend(Path(x) for x in hit[1])
        return HOLD_PROBES
    INSTR["hold_probe_miss"] += 1
    if not p.exists():
        HOLD_PROBE_WIN[wkey] = (fp, ())
        return HOLD_PROBES
    if p.is_dir():
        store = p / "store.db"
        if store.exists():
            HOLD_PROBES.extend((store, p / "store.db-wal", p / "store.db-shm"))
        else:
            HOLD_PROBES.append(p)
    else:
        HOLD_PROBES.append(p)
    HOLD_PROBE_WIN[wkey] = (fp, tuple(str(x) for x in HOLD_PROBES))
    return HOLD_PROBES

def _parse_lsof_Fn(stdout: str) -> dict[str, list[int]]:
    global _LSOF_CUR_PID
    _LSOF_BY.clear()
    _LSOF_CUR_PID = None
    for line in (stdout or "").splitlines():
        if not line:
            continue
        tag, rest = line[0], line[1:]
        if tag == "p":
            try:
                _LSOF_CUR_PID = int(rest)
            except ValueError:
                _LSOF_CUR_PID = None
        elif tag == "n" and _LSOF_CUR_PID is not None:
            _LSOF_BY[rest].append(_LSOF_CUR_PID)
    return _LSOF_BY

def _lsof_probe_fp(probes: list) -> tuple:
    LSOF_PROBE_FP.clear()
    for p in probes:
        try:
            st = p.stat()
            LSOF_PROBE_FP.append((_du_key(p), st.st_mtime_ns, st.st_ino, st.st_size))
        except OSError:
            LSOF_PROBE_FP.append((_du_key(p), 0, 0, 0))
    return tuple(LSOF_PROBE_FP)

def lock_pids_many(targets: list[Path], *, fresh: bool = False) -> dict[Path, list[int]]:
    """Probe holders. Timeout/OSError must NOT cache as unlocked — that is lock-rot."""
    LSOF_OUT.clear()
    LSOF_SEEN.clear()
    for t in targets:
        LSOF_OUT[t] = []
        LSOF_SEEN[t] = set()
        LSOF_UNKNOWN.discard(str(t))
    if not targets:
        LSOF_RESULT.clear()
        return LSOF_RESULT
    _LSOF_PROBES.clear()
    _LSOF_OWNER.clear()
    for t in targets:
        for pr in hold_probes(t):
            if pr.exists():
                _LSOF_PROBES.append(pr)
                _LSOF_OWNER.append(t)
    if not _LSOF_PROBES:
        LSOF_RESULT.clear()
        LSOF_RESULT.update(LSOF_OUT)
        return LSOF_RESULT
    key = "\0".join(sorted({str(p) for p in _LSOF_PROBES}))
    fp = _lsof_probe_fp(_LSOF_PROBES)
    if not fresh:
        hit = _LSOF_CACHE.get(key)
        if hit is not None and hit[0] == fp:
            INSTR["lsof_hit"] += 1
            blob = hit[1]
            for t in targets:
                LSOF_OUT[t] = list(blob.get(str(t), ()))
            LSOF_RESULT.clear()
            LSOF_RESULT.update(LSOF_OUT)
            return LSOF_RESULT
    else:
        INSTR["lsof_fresh"] += 1
        _LSOF_CACHE.pop(key, None)
    INSTR["lsof_miss"] += 1
    LSOF_FMAP.clear()
    probe_ok = False
    try:
        r = subprocess.run(
            ["lsof", "-Fn", *[str(p) for p in _LSOF_PROBES]],
            capture_output=True, text=True, timeout=30,
        )
        LSOF_FMAP.update(_parse_lsof_Fn(r.stdout or ""))
        probe_ok = True
    except subprocess.TimeoutExpired:
        INSTR["lsof_timeout"] += 1
    except OSError:
        INSTR["lsof_oserr"] += 1
    if not probe_ok:
        for t in targets:
            LSOF_UNKNOWN.add(str(t))
            LSOF_OUT[t] = [LSOF_UNKNOWN_PID]  # truthy — never confuse with unlocked []
        # refuse to cache — next caller must re-probe
        LSOF_RESULT.clear()
        LSOF_RESULT.update(LSOF_OUT)
        return LSOF_RESULT
    for pr, t in zip(_LSOF_PROBES, _LSOF_OWNER):
        names = (str(pr),)
        try:
            names = (str(pr), str(pr.resolve()))
        except OSError:
            pass
        for name in names:
            for pid in LSOF_FMAP.get(name, ()):
                if pid not in LSOF_SEEN[t]:
                    LSOF_SEEN[t].add(pid)
                    LSOF_OUT[t].append(pid)
    _LSOF_CACHE[key] = (fp, {str(t): tuple(LSOF_OUT[t]) for t in targets})
    LSOF_RESULT.clear()
    LSOF_RESULT.update(LSOF_OUT)
    return LSOF_RESULT

def lock_unknown(p: Path) -> bool:
    return str(p) in LSOF_UNKNOWN

def lock_pids(p: Path, *, fresh: bool = False) -> list[int]:
    if not fresh and lock_unknown(p):
        INSTR["lsof_unknown_hit"] += 1
        return [LSOF_UNKNOWN_PID]
    if not fresh and _LOCK_SNAP is not None and str(p) in _LOCK_SNAP:
        INSTR["lsof_hit"] += 1
        return list(_LOCK_SNAP[str(p)])
    return lock_pids_many([p], fresh=fresh).get(p, [])

def is_locked(p: Path, *, fresh: bool = False) -> bool:
    return bool(lock_pids(p, fresh=fresh))

def require_unlocked(p: Path, *, verb: str) -> None:
    pids = lock_pids(p, fresh=True)
    if lock_unknown(p) or LSOF_UNKNOWN_PID in pids:
        die(f"REFUSE {verb}: lsof probe failed (timeout/error) — retry; not treating as free")
    if pids:
        die(f"REFUSE {verb}: held pids={pids}")

@dataclass(frozen=True)
class FileSnap:
    path: Path
    mtime_ns: int
    size: int
    root: str | None = None

    @staticmethod
    def take(path: Path, *, with_root: bool = False) -> "FileSnap":
        st = path.stat()
        return FileSnap(path, st.st_mtime_ns, st.st_size,
                        root_of(path) if with_root else None)

    def drifted(self) -> bool:
        if not self.path.exists(): return True
        st = self.path.stat()
        if st.st_mtime_ns != self.mtime_ns or st.st_size != self.size:
            return True
        if self.root is not None and root_of(self.path) != self.root:
            return True
        return False

def clip(s: str | None, n: int = 100) -> str:
    if not s: return ""
    s = " ".join(s.replace("\n", " ").split())
    return s if len(s) <= n else s[: n - 1] + "…"

def slug_cwd(slug: str) -> str:
    s = slug[1:] if slug.startswith("-") else slug
    naive = "/" + s.replace("-", "/")
    idx = _cwd_index()
    if s in idx: return idx[s]
    norm = s.replace("_", "-")
    for enc, path in idx.items():
        if enc.replace("_", "-") == norm: return path
    return naive

def _kids_fp(dirpath: Path) -> tuple:
    try:
        st = dirpath.stat()
        names = sorted(os.listdir(dirpath))
    except OSError:
        return ()
    kids = []
    for name in names:
        if name.startswith("."):
            continue
        p = dirpath / name
        try:
            s = p.stat()
            kids.append((name, s.st_mtime_ns, s.st_ino, s.st_size))
        except OSError:
            pass
    return (st.st_mtime_ns, st.st_ino, tuple(kids))

def _cwd_roots_fp() -> tuple:
    return _kids_fp(HOME / "cl")

def _cwd_index(*, force: bool = False) -> dict[str, str]:
    global _CWD_IDX, _CWD_IDX_FP
    fp = _cwd_roots_fp()
    if not force and _CWD_IDX is not None and _CWD_IDX_FP == fp:
        return _CWD_IDX
    _CWD_IDX = {}
    root = HOME / "cl"
    if root.is_dir():
        base_depth = str(root).count(os.sep)
        for dirpath, dirnames, _ in os.walk(root):
            depth = dirpath.count(os.sep) - base_depth
            if depth > 5:
                dirnames.clear(); continue
            dirnames[:] = [d for d in dirnames if d not in
                           {".git", "node_modules", "venv", ".venv", "dist", "build", "__pycache__", ".tox"}]
            enc = dirpath.lstrip("/").replace("/", "-")
            _CWD_IDX.setdefault(enc, dirpath)
    _CWD_IDX_FP = fp
    return _CWD_IDX

def _store_put(s: "Sess") -> None:
    STORE_IDX[_du_key(s.path)] = s

def _store_drop_kind(kind: str, *, project: str | None = None) -> None:
    for key, s in list(STORE_IDX.items()):
        if s.kind != kind:
            continue
        if project is not None and s.project != project:
            continue
        del STORE_IDX[key]

def _store_drop_under(kind: str, root: Path) -> None:
    try:
        root_r = root.resolve()
    except OSError:
        root_r = root
    for key, s in list(STORE_IDX.items()):
        if s.kind != kind:
            continue
        try:
            pp = s.path.resolve()
        except OSError:
            pp = s.path
        if pp == root_r or root_r in pp.parents:
            del STORE_IDX[key]

def _win_trust(wkey: str, fp: tuple) -> bool:
    if STORE_WIN.get(wkey) == fp:
        INSTR["scan_win_hit"] += 1
        INSTR["scan_trust"] += 1
        return True
    INSTR["scan_win_miss"] += 1
    return False

def _win_put(wkey: str, fp: tuple) -> None:
    STORE_WIN[wkey] = fp

def _scan_cursor_window() -> None:
    if not CURSOR_CHATS.exists():
        _store_drop_kind("cursor")
        for k in list(STORE_WIN):
            if k.startswith("c:"):
                STORE_WIN.pop(k, None)
        return
    root_fp = _kids_fp(CURSOR_CHATS)
    if _win_trust("c:", root_fp):
        return
    seen_proj: set[str] = set()
    for proj in CURSOR_CHATS.iterdir():
        if not proj.is_dir():
            continue
        seen_proj.add(proj.name)
        wkey = "c:" + proj.name
        fp = _kids_fp(proj)
        if _win_trust(wkey, fp):
            continue
        _store_drop_kind("cursor", project=proj.name)
        for chat in proj.iterdir():
            if not chat.is_dir():
                continue
            cfp = _kids_fp(chat)
            size = mtime_ns = None
            for name, mt, _ino, sz in (cfp[2] if cfp else ()):
                if name == "store.db":
                    size, mtime_ns = sz, mt
                    break
            if size is None:
                continue
            _store_put(Sess("cursor", chat.name, chat / "store.db", size / 1e6,
                            mtime_ns / 1e9, project=proj.name))
        _win_put(wkey, fp)
    for key, s in list(STORE_IDX.items()):
        if s.kind == "cursor" and s.project not in seen_proj:
            del STORE_IDX[key]
            STORE_WIN.pop("c:" + s.project, None)
    _win_put("c:", root_fp)

def _codex_sid(name: str) -> str:
    stem = name[:-6] if name.endswith(".jsonl") else name
    parts = stem.split("-")
    return "-".join(parts[-5:]) if len(parts) >= 5 else stem

def _scan_codex_day(day: Path, wkey: str) -> None:
    fp = _kids_fp(day)
    if _win_trust(wkey, fp):
        return
    _store_drop_under("codex", day)
    for name, mt, _ino, sz in (fp[2] if fp else ()):
        if not (name.startswith("rollout-") and name.endswith(".jsonl")):
            continue
        _store_put(Sess("codex", _codex_sid(name), day / name, sz / 1e6, mt / 1e9))
    _win_put(wkey, fp)

def _scan_codex_month(month: Path, wkey: str) -> None:
    fp = _kids_fp(month)
    if _win_trust(wkey, fp):
        return
    live = set()
    for day in month.iterdir() if month.is_dir() else []:
        if not day.is_dir():
            continue
        live.add(day.name)
        _scan_codex_day(day, wkey + "/" + day.name)
    for k in list(STORE_WIN):
        if k.startswith(wkey + "/") and k[len(wkey) + 1:].split("/")[0] not in live:
            STORE_WIN.pop(k, None)
    _win_put(wkey, fp)

def _scan_codex_year(year: Path, wkey: str) -> None:
    fp = _kids_fp(year)
    if _win_trust(wkey, fp):
        return
    live = set()
    for month in year.iterdir() if year.is_dir() else []:
        if not month.is_dir():
            continue
        live.add(month.name)
        _scan_codex_month(month, wkey + "/" + month.name)
    for k in list(STORE_WIN):
        if k.startswith(wkey + "/") and k[len(wkey) + 1:].split("/")[0] not in live:
            STORE_WIN.pop(k, None)
    _win_put(wkey, fp)

def _scan_codex_window() -> None:
    if not CODEX_SESS.exists():
        _store_drop_kind("codex")
        for k in list(STORE_WIN):
            if k == "x:" or k.startswith("x:/"):
                STORE_WIN.pop(k, None)
        return
    fp = _kids_fp(CODEX_SESS)
    if _win_trust("x:", fp):
        return
    live = set()
    for year in CODEX_SESS.iterdir():
        if not year.is_dir():
            continue
        live.add(year.name)
        _scan_codex_year(year, "x:/" + year.name)
    for k in list(STORE_WIN):
        if k.startswith("x:/") and k[3:].split("/")[0] not in live:
            STORE_WIN.pop(k, None)
    for key, s in list(STORE_IDX.items()):
        if s.kind == "codex":
            try:
                if CODEX_SESS.resolve() not in s.path.resolve().parents:
                    del STORE_IDX[key]
            except OSError:
                pass
    _win_put("x:", fp)

def _scan_claude_window() -> None:
    if not CLAUDE_PROJS.exists():
        _store_drop_kind("claude")
        for k in list(STORE_WIN):
            if k == "l:" or k.startswith("l:"):
                STORE_WIN.pop(k, None)
        return
    fp = _kids_fp(CLAUDE_PROJS)
    if _win_trust("l:", fp):
        return
    seen = set()
    for proj in CLAUDE_PROJS.iterdir():
        if not proj.is_dir() or proj.name == "memory":
            continue
        seen.add(proj.name)
        wkey = "l:" + proj.name
        pfp = _kids_fp(proj)
        if _win_trust(wkey, pfp):
            continue
        _store_drop_kind("claude", project=proj.name)
        for name, mt, _ino, sz in (pfp[2] if pfp else ()):
            if not name.endswith(".jsonl"):
                continue
            _store_put(Sess("claude", Path(name).stem, proj / name, sz / 1e6, mt / 1e9,
                            project=proj.name))
        _win_put(wkey, pfp)
    for key, s in list(STORE_IDX.items()):
        if s.kind == "claude" and s.project not in seen:
            del STORE_IDX[key]
            STORE_WIN.pop("l:" + s.project, None)
    _win_put("l:", fp)

def _tx_fp() -> tuple:
    """Fingerprint nested agent-transcripts — project kids alone are blind."""
    if not CURSOR_PROJS.exists():
        return ()
    parts = []
    try:
        names = sorted(os.listdir(CURSOR_PROJS))
    except OSError:
        return ()
    for name in names:
        if name.startswith("."):
            continue
        at = CURSOR_PROJS / name / "agent-transcripts"
        parts.append((name, _kids_fp(at) if at.is_dir() else ()))
    return tuple(parts)

def transcript_index() -> dict:
    global TX_WIN
    if not CURSOR_PROJS.exists():
        TX_IDX.clear()
        TX_WIN = ()
        return TX_IDX
    fp = _tx_fp()
    if TX_WIN == fp and TX_IDX:
        INSTR["tx_win_hit"] += 1
        return TX_IDX
    INSTR["tx_win_miss"] += 1
    TX_IDX.clear()
    for proj_name, _at_fp in fp:
        at = CURSOR_PROJS / proj_name / "agent-transcripts"
        if not at.is_dir():
            continue
        try:
            sids = os.listdir(at)
        except OSError:
            continue
        for sid in sids:
            if sid.startswith("."):
                continue
            sid_dir = at / sid
            if not sid_dir.is_dir():
                continue
            jl = sid_dir / f"{sid}.jsonl"
            if jl.exists():
                TX_IDX[sid] = (jl, proj_name)
    TX_WIN = fp
    return TX_IDX

ENRICH_TAIL = 96_000   # last prompt lives near EOF; 96KB is enough
ENRICH_HEAD = 32_000   # codex session_meta is at the start

def tail_bytes(p: Path, n: int = 400_000) -> bytes:
    with open(p, "rb") as f:
        f.seek(0, 2); sz = f.tell(); f.seek(max(0, sz - n)); return f.read()

def head_bytes(p: Path, n: int = 256_000) -> bytes:
    with open(p, "rb") as f: return f.read(n)

def iter_jsonl_reverse(blob: bytes, *, kind: str, sid: str):
    """Newest-first lines; O(1) aux — walk newlines backward, no ends[]."""
    n = len(blob)
    end = n
    while end > 0:
        nl = blob.rfind(b"\n", 0, end)
        start = 0 if nl < 0 else nl + 1
        if start < end:
            line = blob[start:end]
            if line.strip():
                try:
                    yield json.loads(line), start
                except Exception as e:
                    bump_coarse("enrich_json_skip")
                    ENRICH_SKIPS.append(dict(
                        kind=kind, sid=sid[:48], off=start, n=len(line), err=type(e).__name__))
        if nl < 0:
            break
        end = nl

@dataclass
class Sess:
    kind: str
    sid: str
    path: Path
    mb: float
    mtime: float
    scan_saw_lock: bool = False
    cwd: str = ""
    last_user: str = ""
    last_asst: str = ""
    project: str = ""
    extra: str = ""
    enrich_fp: object | None = None

    @property
    def locked(self) -> bool:
        return is_locked(self.path)

    @property
    def chat_dir(self) -> Path | None:
        return self.path.parent if self.kind == "cursor" else None

def text_from_message_content(c) -> str:
    if isinstance(c, str): return c
    if isinstance(c, list):
        TEXT_PARTS.clear()
        for x in c:
            if isinstance(x, dict):
                if x.get("type") in ("text", "input_text") and x.get("text"):
                    TEXT_PARTS.append(x["text"])
                elif x.get("type") == "tool_result":
                    continue
            elif isinstance(x, str):
                TEXT_PARTS.append(x)
        return " ".join(TEXT_PARTS)
    return ""

def iter_jsonl(blob: bytes, *, kind: str, sid: str):
    start = 0
    n = len(blob)
    while start < n:
        nl = blob.find(b"\n", start)
        end = n if nl < 0 else nl
        line = blob[start:end]
        if line.strip():
            try:
                yield json.loads(line), start
            except Exception as e:
                bump_coarse("enrich_json_skip")
                ENRICH_SKIPS.append(dict(
                    kind=kind, sid=sid[:48], off=start, n=len(line), err=type(e).__name__))
        start = end + 1 if nl >= 0 else n

def _enrich_cursor(s):
    hit = transcript_index().get(s.sid)
    if not hit:
        return
    jl, proj_name = hit
    s.project = proj_name
    s.cwd = slug_cwd(proj_name)
    try:
        s.extra = f"transcript {round(jl.stat().st_size/1e6,1)}MB"
    except OSError:
        s.extra = "transcript"
    for o, _off in iter_jsonl_reverse(tail_bytes(jl, ENRICH_TAIL), kind="cursor", sid=s.sid):
        role = o.get("role"); msg = o.get("message") or {}
        t = text_from_message_content(msg.get("content") if isinstance(msg, dict) else o.get("content"))
        if role == "user" and t and not s.last_user:
            if not t.startswith("<"):
                s.last_user = t
            elif "user_query>" in t:
                i = t.find("<user_query>"); j = t.find("</user_query>")
                s.last_user = t[i + 12: j if j > 0 else None]
        elif role == "assistant" and t and not s.last_asst:
            s.last_asst = t
        if s.last_user and s.last_asst:
            break
    try:
        con = open_ro(s.path)
        meta = json.loads(bytes.fromhex(con.execute("SELECT value FROM meta WHERE key='0'").fetchone()[0]).decode())
        con.close()
        if meta.get("name"):
            s.extra = (s.extra + " · " if s.extra else "") + str(meta["name"])[:40]
    except Exception as e:
        record_exception("enrich.cursor_meta", e)

def _enrich_codex(s):
    for o, _off in iter_jsonl(head_bytes(s.path, ENRICH_HEAD), kind="codex", sid=s.sid):
        if o.get("type") == "session_meta":
            pl = o.get("payload") or {}
            s.cwd = pl.get("cwd") or s.cwd
            s.sid = pl.get("session_id") or s.sid
            break
    for o, _off in iter_jsonl_reverse(tail_bytes(s.path, ENRICH_TAIL), kind="codex", sid=s.sid):
        typ, pl = o.get("type"), o.get("payload") or {}
        if (not s.last_user and typ == "response_item"
                and pl.get("type") == "message" and pl.get("role") == "user"):
            t = text_from_message_content(pl.get("content"))
            if t and "environment_context" not in t[:80]:
                s.last_user = t
        elif not s.last_asst and typ == "event_msg" and pl.get("type") == "task_complete":
            s.last_asst = str(pl.get("last_agent_message") or "")
        elif (not s.last_asst and typ == "response_item" and pl.get("role") == "assistant"):
            t = text_from_message_content(pl.get("content"))
            if t:
                s.last_asst = t
        if s.last_user and s.last_asst:
            break

def _enrich_claude(s):
    s.project = s.path.parent.name
    s.cwd = slug_cwd(s.project)
    for o, _off in iter_jsonl_reverse(tail_bytes(s.path, ENRICH_TAIL), kind="claude", sid=s.sid):
        if o.get("cwd"):
            s.cwd = o["cwd"]
        if not s.last_user and o.get("type") == "user":
            t = text_from_message_content((o.get("message") or {}).get("content"))
            if t and "tool_result" not in t[:40] and not t.startswith("<local-command"):
                s.last_user = t
        elif not s.last_asst and o.get("type") == "assistant":
            t = text_from_message_content((o.get("message") or {}).get("content"))
            if t:
                s.last_asst = t
        if s.last_user and s.last_asst:
            break

def enrich_sess(s):
    """Fill cwd / last prompt via KIND driver."""
    d = KIND.get(s.kind)
    if d is None:
        return
    d.enrich(s)

def scan_all(min_mb=20.0, kinds=None, limit=0):
    """Inventory sessions ≥min_mb; always enrich (cwd/prompt) — not optional."""
    want = set(kinds) if kinds else set(KINDS)
    for name in KINDS:
        if name in want:
            KIND[name].scan()
    SESSIONS.clear()
    for s in STORE_IDX.values():
        if s.kind in want and s.mb >= min_mb:
            SESSIONS.append(s)
    SESSIONS.sort(key=lambda s: -s.mb)
    if limit and limit > 0:
        del SESSIONS[limit:]
    _cwd_index()
    for s in SESSIONS:
        efp = (s.mtime, s.mb)
        if s.enrich_fp == efp and (s.cwd or s.last_user or s.extra):
            INSTR["enrich_win_hit"] += 1
            continue
        try:
            enrich_sess(s)
            s.enrich_fp = efp
        except Exception as e:
            s.extra = f"enrich-err:{e}"
            s.enrich_fp = None
    return SESSIONS

def print_table(rows):
    global _LOCK_SNAP
    if not rows:
        print("(no sessions ≥ threshold)"); return
    tot = sum(s.mb for s in rows)

    snap = lock_pids_many([s.path for s in rows])
    _LOCK_SNAP = {str(p): pids for p, pids in snap.items()}
    try:
        print(f"\n{'#':>3} {'kind':<7} {'MB':>8} {'lock':<5} {'id':<10}  cwd / last prompt")
        print("-" * 100)
        for i, s in enumerate(rows, 1):
            print(f"{i:3} {s.kind:<7} {s.mb:8.1f} {'LOCK' if s.locked else 'ok':<5} {s.sid[:10]:<10}  {clip(s.cwd, 48) or '—'}")
            if s.last_user: print(f"{'':3} {'':7} {'':8} {'':5} {'':10}  user: {clip(s.last_user, 88)}")
            if s.last_asst: print(f"{'':3} {'':7} {'':8} {'':5} {'':10}  asst: {clip(s.last_asst, 88)}")
            if s.extra: print(f"{'':3} {'':7} {'':8} {'':5} {'':10}  {clip(s.extra, 88)}")
        print("-" * 100)
        print(f"{len(rows)} sessions · {tot/1024:.2f} GB listed\n")
    finally:
        _LOCK_SNAP = None

def _varint(buf, i):
    v = s = 0
    while i < len(buf) and s < 64:
        b = buf[i]; i += 1; v |= (b & 0x7F) << s
        if not (b & 0x80): return v, i
        s += 7
    return None

def fields(buf: bytes):
    i = n = 0
    while i < len(buf) and n < 2_000_000:
        n += 1; start = i; p = _varint(buf, i)
        if not p: return
        key, i = p; f, wt = key >> 3, key & 7
        if f <= 0: return
        if wt == 0:
            p = _varint(buf, i)
            if not p: return
            _, i = p; yield f, wt, None
        elif wt == 1: i += 8; yield f, wt, None
        elif wt == 5: i += 4; yield f, wt, None
        elif wt == 2:
            p = _varint(buf, i)
            if not p: return
            ln, i = p
            if ln < 0 or i + ln > len(buf): return
            yield f, wt, buf[i:i + ln]; i += ln
        else: return
        if i <= start: return

def as_id(v: bytes) -> str | None:
    return v.hex() if len(v) == 32 else None

def blob_head_kind(data: bytes) -> str:
    """O(1) head classifier — separates source/text orphans from protobuf roots.

    Earned: tip large-orphan mass labeled empty_declare was #import <Foundation/…>
    (Metal headers), not agent protobuf. declare_root-on-text → 0 refs = false label.
    Earned: tip top-size orphans were 'binary' but head \\x0a\\x20 = protobuf field1 LD(32)
    (embedded 32-byte id) — not gzip/image; name that family so GC/fence can see it.
    """
    if not data:
        return "empty"
    # protobuf: field 1, wire 2, length 32 → embedded blob id (common agent envelope)
    if len(data) >= 34 and data[0] == 0x0A and data[1] == 0x20:
        return "pb_f1_id32"
    s = data[:200]
    if s.startswith((b"#import ", b"#include ")):
        return "objc_hdr"
    ls = s.lstrip()
    if ls.startswith((b"package ", b"import ")):
        return "source_import"
    if s.startswith((b"<!DOCTYPE", b"<html", b"<?xml")):
        return "markup"
    if s[:1] in (b"{", b"["):
        return "jsonish"
    pr = sum(1 for b in s if 32 <= b < 127 or b in (9, 10, 13)) / max(1, len(s))
    if pr > 0.85:
        return "textish"
    return "binary"

def admit(law: L, nbytes: int, recent=False) -> bool:
    if law in (L.MUST, L.SEAL): return True
    if law is L.RS: return recent and nbytes <= MAX_LEAF
    if law is L.PROBE: return nbytes <= MAX_LEAF
    raise RuntimeError(law)

def _view_clear() -> None:
    _TURNS.clear(); _ALWAYS.clear(); _HEADERS.clear()
    _MAPS.clear(); _UNKNOWN.clear(); _REFS.clear()

def declare_root(data: bytes) -> tuple[View, list[Ref]]:
    _view_clear()
    for f, wt, val in fields(data):
        if wt != 2 or val is None: continue
        if f in (12, 31):
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ef == 2 and (hid := as_id(ev)):
                    _MAPS.append((f, hid)); _REFS.append(Ref(hid, L.MUST, f"map{f}"))
            continue
        hid = as_id(val)
        if not hid: continue
        law = ROOT_LAW.get(f)
        if f == 8:
            _TURNS.append(hid); _ALWAYS.append((f, hid)); _REFS.append(Ref(hid, L.MUST, "f8"))
        elif law == "MUST":
            _ALWAYS.append((f, hid)); _REFS.append(Ref(hid, L.MUST, f"f{f}"))
        elif law == "SEAL":
            _HEADERS.append((f, hid)); _REFS.append(Ref(hid, L.SEAL, f"f{f}"))
        elif law is None:
            _UNKNOWN.append((f, hid)); _REFS.append(Ref(hid, L.PROBE, f"f{f}"))
    return (View(list(_TURNS), list(_ALWAYS), list(_HEADERS), list(_MAPS), list(_UNKNOWN)),
            list(_REFS))

def _edge_add(val, kind, law) -> None:
    hid = as_id(val)
    if hid and hid not in _EDGE_SEEN:
        _EDGE_SEEN.add(hid)
        _EDGE.append(Ref(hid, law, kind))

def turn_edges(data: bytes) -> list[Ref]:
    _EDGE.clear(); _EDGE_SEEN.clear()
    for f, wt, val in fields(data):
        if wt != 2 or val is None: continue
        if f == 1:
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ev is not None:
                    if ef == 1: _edge_add(ev, "user_message", L.MUST)
                    elif ef == 2: _edge_add(ev, "step", L.RS)
        elif f == 2:
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ev is not None:
                    if ef == 1: _edge_add(ev, "shell_command", L.MUST)
                    elif ef == 2: _edge_add(ev, "shell_output", L.RS)
    return list(_EDGE)

class Snap:
    __slots__ = ("path", "con", "blob", "ln", "gets", "meta_rows", "meta", "_slot")
    def __init__(self, path: Path):
        global _SNAP_SLOT
        if _SNAP_SLOT >= 2:
            die(f"snap nest depth {_SNAP_SLOT}")
        self._slot = _SNAP_SLOT
        _SNAP_SLOT += 1
        self.path = path
        self.con = open_ro(path)
        self.con.execute("BEGIN")
        if self._slot == 0:
            self.blob, self.ln = _SNAP_BLOB_A, _SNAP_LN_A
        else:
            self.blob, self.ln = _SNAP_BLOB_B, _SNAP_LN_B
        self.blob.clear(); self.ln.clear()
        self.gets = 0
        self.meta_rows = list(self.con.execute("SELECT key,value FROM meta"))
        self.meta = json.loads(bytes.fromhex(dict(self.meta_rows)["0"]).decode())
    def __enter__(self): return self
    def __exit__(self, *a):
        global _SNAP_SLOT
        try: self.con.execute("ROLLBACK")
        except sqlite3.Error: pass
        self.con.close()
        self.blob.clear(); self.ln.clear()
        _SNAP_SLOT -= 1
    def get(self, hid: str) -> bytes | None:
        if hid in self.blob: return self.blob[hid]
        self.gets += 1
        row = self.con.execute("SELECT data FROM blobs WHERE id=?", (hid,)).fetchone()
        d = None if not row else bytes(row[0])
        self.blob[hid] = d; self.ln[hid] = None if d is None else len(d); return d
    def length(self, hid: str) -> int | None:
        if hid in self.ln: return self.ln[hid]
        if hid in self.blob: return None if self.blob[hid] is None else len(self.blob[hid])
        row = self.con.execute("SELECT LENGTH(data) FROM blobs WHERE id=?", (hid,)).fetchone()
        self.ln[hid] = None if not row else row[0]; return self.ln[hid]
    def has(self, hid: str) -> bool: return self.length(hid) is not None
    def tip(self) -> str: return self.meta["latestRootBlobId"]

def _plan_clear(root: str, agent, meta_rows) -> None:
    global PLAN_ROOT, PLAN_AGENT, PLAN_BYTES
    PLAN_ROOT = root
    PLAN_AGENT = agent
    PLAN_BYTES = 0
    PLAN_META_ROWS.clear(); PLAN_META_ROWS.extend(meta_rows)
    PLAN_KEEP.clear(); PLAN_DROP.clear(); PLAN_MISSING.clear()
    PLAN_TURNS.clear(); PLAN_RECENT.clear()

def _plan_add(hid, reason, n) -> None:
    global PLAN_BYTES
    if hid not in PLAN_KEEP:
        PLAN_KEEP[hid] = reason
        PLAN_BYTES += n

class Plan:
    __slots__ = ()
    @property
    def root(self): return PLAN_ROOT
    @property
    def agent_id(self): return PLAN_AGENT
    @property
    def meta_rows(self): return PLAN_META_ROWS
    @property
    def keep(self): return PLAN_KEEP
    @property
    def drop(self): return PLAN_DROP
    @property
    def missing(self): return PLAN_MISSING
    @property
    def turns(self): return PLAN_TURNS
    @property
    def recent(self): return PLAN_RECENT
    @property
    def bytes_est(self): return PLAN_BYTES
    def add(self, hid, reason, n): _plan_add(hid, reason, n)

_PLAN = Plan()

def _put(hid, law, tag, data, recent=False, req=False):
    if data is None:
        if req or law is L.MUST: PLAN_MISSING.append(f"{tag}:{hid}")
        return
    if law in (L.MUST, L.SEAL) or admit(law, len(data), recent):
        _plan_add(hid, f"{tag}:{law.name}", len(data))
    elif law is L.RS:
        PLAN_DROP[hid] = f"{tag}:{'old_turn' if not recent else f'recent_large:{len(data)}'}"
    else:
        PLAN_DROP[hid] = f"{tag}:probe_large:{len(data)}"

def plan_from(snap: Snap, recent_n: int = DEFAULT_RECENT) -> Plan:
    m = snap.meta; root = m["latestRootBlobId"]
    if not root or len(root) != 64: die(f"bad root {root!r}")
    _plan_clear(root, m.get("agentId"), snap.meta_rows)
    rd = snap.get(root)
    if rd is None: die("root missing")
    _plan_add(root, "root:MUST", len(rd))
    view, refs = declare_root(rd)
    PLAN_TURNS.extend(view.turns)
    PLAN_RECENT.extend(view.turns[-recent_n:])
    if len(PLAN_TURNS) < MIN_TURNS:
        raise SkipChat(f"too_few_turns:{len(PLAN_TURNS)}")
    _RECENT_SET.clear()
    _RECENT_SET.update(PLAN_RECENT)
    for r in refs:
        _put(r.id, r.law, r.tag, snap.get(r.id), req=r.law in (L.MUST, L.SEAL))
    for tid in PLAN_TURNS:
        td = snap.get(tid)
        if td is None: PLAN_MISSING.append(f"turn:{tid}"); continue
        for e in turn_edges(td):
            _put(e.id, e.law, e.tag, snap.get(e.id), recent=tid in _RECENT_SET, req=e.law is L.MUST)
    for f, sid in list(view.maps):
        if f != 31: continue
        sd = snap.get(sid)
        if not sd: continue
        for fn, wt, val in fields(sd):
            if not (wt == 2 and fn == 1 and val is not None): continue
            nv, nrefs = declare_root(val)
            for r in nrefs:
                _put(r.id, r.law, f"sub.{r.tag}", snap.get(r.id))
            for th in list(nv.turns):
                td = snap.get(th)
                if not td: continue
                for e in turn_edges(td):
                    if e.law is L.MUST:
                        _put(e.id, e.law, f"sub.{e.tag}", snap.get(e.id))
            break
    if PLAN_BYTES > MAX_BYTES or len(PLAN_KEEP) > MAX_BLOBS:
        die(f"over-collect {len(PLAN_KEEP)} / {PLAN_BYTES}")
    req = [x for x in PLAN_MISSING if not x.startswith(("step", "shell_output"))]
    if req: die(f"source missing {req[:6]}")
    recount_admit_buckets()
    return _PLAN

def materialize(snap: Snap, dst: Path, plan: Plan) -> dict:
    if dst.exists(): retire(dst)
    g0 = snap.gets; t0 = time.time()
    MAT_ROWS.clear()
    d = sqlite3.connect(dst)
    try:
        d.execute("PRAGMA journal_mode=OFF"); d.execute("PRAGMA synchronous=OFF")
        d.execute("CREATE TABLE blobs(id TEXT PRIMARY KEY, data BLOB)")
        d.execute("CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT)")
        d.executemany("INSERT INTO meta VALUES(?,?)", plan.meta_rows)
        kept = 0
        for hid, reason in plan.keep.items():
            data = snap.get(hid)
            if data is None: die(f"vanished {hid[:12]} {reason}")
            MAT_ROWS.append((hid, data)); kept += len(data)
        d.executemany("INSERT INTO blobs VALUES(?,?)", MAT_ROWS); d.commit()
        if d.execute("PRAGMA integrity_check").fetchone()[0] != "ok": die("integrity")
    finally: d.close()
    return dict(root=plan.root, drift=snap.tip() != plan.root, blobs=len(plan.keep),
                mb=round(kept / 1e6, 2), turns=len(plan.turns), drop_n=len(plan.drop),
                materialize_sql_gets=snap.gets - g0, seconds=round(time.time() - t0, 2),
                agentId=plan.agent_id)

def project(src: Path, dst: Path, recent_n: int = DEFAULT_RECENT) -> dict:
    with Snap(src) as s:
        return materialize(s, dst, plan_from(s, recent_n))

def meta_of(con) -> dict:
    return json.loads(bytes.fromhex(con.execute("SELECT value FROM meta WHERE key='0'").fetchone()[0]).decode())

def root_of(p: Path) -> str | None:
    if not p.exists():
        return None
    try:
        con = open_ro(p)
        try:
            return meta_of(con).get("latestRootBlobId")
        finally:
            con.close()
    except Exception:
        return None

def write_reach_meta(chat: Path, *, source_root: str | None, snap: FileSnap,
                     coherent: bool) -> None:
    META_SCRATCH.clear()
    META_SCRATCH.update(
        v=2,
        source_root=source_root,
        source_mtime_ns=snap.mtime_ns,
        source_size=snap.size,
        coherent=coherent,
        cut_ts=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )
    (chat / REACH_META_NAME).write_text(json.dumps(META_SCRATCH, separators=(",", ":")))

def read_reach_meta(chat: Path) -> dict | None:
    p = chat / REACH_META_NAME
    if not p.exists(): return None
    try: return json.loads(p.read_text())
    except Exception: return None

def live_fingerprint(live: Path) -> StoreFingerprint | None:
    try:
        st = live.stat()
    except OSError:
        return None
    return StoreFingerprint(root_of(live), st.st_mtime_ns, st.st_size)

def meta_fingerprint(meta: dict | None) -> StoreFingerprint | None:
    if not meta:
        return None
    return StoreFingerprint(meta.get("source_root"), meta.get("source_mtime_ns"), meta.get("source_size"))

def fingerprint_mismatch(live_fp: StoreFingerprint, meta_fp: StoreFingerprint, *, mutated_why: str, root_why: str) -> str | None:
    if meta_fp.root and live_fp.root and meta_fp.root != live_fp.root:
        return root_why
    if meta_fp.mtime_ns != live_fp.mtime_ns or meta_fp.size != live_fp.size:
        return mutated_why
    return None

def judge_reach(chat):
    live, reach = chat / "store.db", chat / REACH_NAME
    if not live.exists():
        return False, "no_live"
    live_fp = live_fingerprint(live)
    if live_fp is None:
        return False, "no_live"
    if not reach.exists():
        sm = read_settled(chat)
        mfp = meta_fingerprint(sm)
        if mfp is not None:
            drift = fingerprint_mismatch(live_fp, mfp,
                              mutated_why="live_mutated_since_settled",
                              root_why="settled_root_diverged")
            if drift:
                return False, drift
            return True, "settled_marker"
        return False, "no_reachable"
    meta = read_reach_meta(chat)
    rr = root_of(reach)
    if not meta:
        if live_fp.root and rr and live_fp.root == rr:
            return True, "root_match_legacy"
        return False, "root_diverged_legacy"
    if meta.get("locked_during_prep"):
        return False, "prep_while_locked"
    if meta.get("coherent") is False:
        return False, "prep_saw_drift"
    mfp = meta_fingerprint(meta)
    drift = fingerprint_mismatch(live_fp, mfp,
                      mutated_why="live_mutated_since_prep",
                      root_why="root_diverged")
    if drift:
        return False, drift
    if live_fp.root and rr and live_fp.root != rr:
        return False, "root_diverged"
    return True, "meta_ok"

def list_sibling_paths(chat: Path) -> list[Path]:
    SIB_PATHS.clear()
    wkey = _du_key(chat)
    fp = _kids_fp(chat)
    hit = SIB_WIN.get(wkey)
    if hit is not None and hit[0] == fp:
        INSTR["sib_win_hit"] += 1
        for p in hit[1]:
            SIB_PATHS[Path(p)] = None
        return list(SIB_PATHS)
    INSTR["sib_win_miss"] += 1
    for pat in SIBLING_GLOBS:
        for p in chat.glob(pat):
            if p.name == "store.db":
                continue
            try:
                key = p.resolve()
            except OSError:
                key = p
            SIB_PATHS[key] = None
    SIB_WIN[wkey] = (fp, tuple(str(k) for k in SIB_PATHS))
    return list(SIB_PATHS)

def bound_sibling_bytes(chat: Path) -> int:
    sib = 0
    for p in list_sibling_paths(chat):
        try: sib += p.stat().st_size
        except OSError: pass
    reach = chat / REACH_NAME
    if reach.exists():
        try: sib += reach.stat().st_size
        except OSError: pass
    return sib

def disk_bound_mb(chat: Path) -> float:
    live = chat / "store.db"
    try:
        live_b = live.stat().st_size if live.exists() else 0
    except OSError:
        live_b = 0
    return (live_b + bound_sibling_bytes(chat)) / 1e6

def phase_kind(fresh: bool, why: str) -> str:
    if not fresh:
        return "STALE"
    if why == "settled_marker":
        return "SETTLED"
    return "REACH"

def cursor_phase(chat: Path) -> dict:
    live = chat / "store.db"
    pids = lock_pids(chat, fresh=True) if live.exists() else []
    fresh, why = judge_reach(chat)
    kind = phase_kind(fresh, why)
    locked = 1 if pids else 0
    allow = PHASE_ALLOW[(locked, kind)]
    state = f"{'LOCKED' if locked else 'UNLOCKED'}_{'FRESH' if fresh else 'STALE'}"
    live_b = live.stat().st_size if live.exists() else 0
    sib = bound_sibling_bytes(chat)
    PHASE.clear()
    PHASE["state"] = state
    PHASE["kind"] = kind
    PHASE["why"] = why
    PHASE["pids"] = pids
    PHASE["allow"] = allow._asdict()
    PHASE["live_mb"] = round(live_b / 1e6, 2)
    PHASE["sibling_mb"] = round(sib / 1e6, 2)
    PHASE["disk_bound_mb"] = round((live_b + sib) / 1e6, 2)
    return dict(PHASE)

def smoke(db: Path) -> dict:
    SMOKE_ERR.clear()
    SMOKE_REP.clear()
    with Snap(db) as s:
        root = s.meta["latestRootBlobId"]; rd = s.get(root)
        if not rd:
            SMOKE_REP.update(ok=False, errors=["root missing"])
            return SMOKE_REP
        view, _ = declare_root(rd)
        loaded = ok = 0
        for tid in view.turns:
            td = s.get(tid)
            if not td: SMOKE_ERR.append(f"missing turn {tid[:12]}"); continue
            loaded += 1
            for e in turn_edges(td):
                if e.law is L.MUST:
                    if s.has(e.id): ok += 1
                    else: SMOKE_ERR.append(f"missing {e.tag} {tid[:12]}")
        key = s.meta.get("blobEncryptionKey") or ""
        if not (isinstance(key, str) and len(key) == 64): SMOKE_ERR.append("bad enc key")
        if not s.meta.get("agentId"): SMOKE_ERR.append("no agentId")
        SMOKE_REP.update(ok=not SMOKE_ERR, errors=SMOKE_ERR[:8], turns=len(view.turns),
                         loaded=loaded, required_ok=ok, agentId=s.meta.get("agentId"),
                         root=root, name=s.meta.get("name"))
        return SMOKE_REP

def falsify(db: Path, against: Path | None = None, recent_n: int = DEFAULT_RECENT) -> dict:
    FALSIFY_ALARMS.clear()
    FALSIFY_INFO.clear()
    FALSIFY_REP.clear()
    with Snap(db) as dst:
        root = dst.meta["latestRootBlobId"]; rd = dst.get(root)
        if not rd:
            FALSIFY_REP.update(ok=False, alarms=["FAIL_ROOT_MISSING"], info={})
            return FALSIFY_REP
        view, _ = declare_root(rd)
        n = dst.con.execute("SELECT COUNT(*) FROM blobs").fetchone()[0]
        payload = dst.con.execute("SELECT SUM(LENGTH(data)) FROM blobs").fetchone()[0] or 0
        FALSIFY_INFO.update(root=root, turns=len(view.turns), blobs=n, mb=round(payload / 1e6, 2),
                            agentId=dst.meta.get("agentId"))
        miss = [f"f{f}:{h[:12]}" for f, h in view.always if not dst.has(h)]
        if miss: FALSIFY_ALARMS.append(f"FAIL_ALWAYS {miss[:4]}")
        if against:
            with Snap(against) as base:
                br = base.meta["latestRootBlobId"]
                FALSIFY_INFO["against"] = br
                FALSIFY_INFO["fresh"] = br == root
                if br != root: FALSIFY_ALARMS.append("FAIL_FRESH")
                else:
                    bd = base.get(br)
                    if bd:
                        lv, lrefs = declare_root(bd)
                        m2 = [f"{r.tag}:{r.id[:12]}" for r in lrefs if r.law is L.MUST and base.length(r.id) is not None and not dst.has(r.id)]
                        if m2: FALSIFY_ALARMS.append(f"FAIL_POLICY {m2[:4]}")
                        small = 0
                        for tid in set(lv.turns[-recent_n:]):
                            td = base.get(tid)
                            if not td: continue
                            for e in turn_edges(td):
                                if e.law is not L.RS or dst.has(e.id): continue
                                ln = base.length(e.id)
                                if ln is not None and ln <= MAX_LEAF: small += 1
                        if small: FALSIFY_ALARMS.append(f"FAIL_RECENT_SMALL {small}")
        sm = smoke(db)
        FALSIFY_INFO["smoke"] = dict(sm)
        if not sm["ok"]: FALSIFY_ALARMS.append(f"FAIL_SMOKE {sm['errors'][:2]}")
        if not (MIN_BLOBS <= n <= MAX_BLOBS): FALSIFY_ALARMS.append(f"FAIL_COUNT {n}")
        if rd[:2] != b"\x0a\x20": FALSIFY_ALARMS.append("FAIL_CRYPTO")
        FALSIFY_REP.update(ok=not FALSIFY_ALARMS, alarms=list(FALSIFY_ALARMS), info=dict(FALSIFY_INFO))
        return FALSIFY_REP

def find_transcript(aid: str) -> Path | None:
    """O(1) after transcript_index amortize — never rescan projects."""
    hit = transcript_index().get(aid)
    return hit[0] if hit else None

def _discard_reach(chat: Path) -> None:
    for name in (REACH_NAME, REACH_META_NAME, "store.db.reachable.building"):
        p = chat / name
        if p.exists() or p.is_symlink():
            retire(p)

def write_settled(chat: Path, snap: FileSnap, *, source_root: str | None) -> None:
    META_SCRATCH.clear()
    META_SCRATCH.update(
        v=1,
        source_root=source_root,
        source_mtime_ns=snap.mtime_ns,
        source_size=snap.size,
        cut_ts=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
    )
    (chat / SETTLED_NAME).write_text(json.dumps(META_SCRATCH, separators=(",", ":")))

def read_settled(chat: Path) -> dict | None:
    p = chat / SETTLED_NAME
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text())
    except Exception:
        return None

def _discard_settled(chat: Path) -> None:
    p = chat / SETTLED_NAME
    if p.exists() or p.is_symlink():
        retire(p)

def prep_cut_sibling(chat: Path, recent_n: int = DEFAULT_RECENT) -> dict:
    live, reach = chat / "store.db", chat / REACH_NAME
    if not live.exists(): die(f"no store.db in {chat}")
    with open(live, "rb") as f:
        if f.read(15) != b"SQLite format 3":
            die(f"not a sqlite store.db ({chat.name})")
    require_unlocked(chat, verb="prep")
    _discard_settled(chat)
    snap = FileSnap.take(live, with_root=True)
    tmp = chat / "store.db.reachable.building"
    if tmp.exists() or tmp.is_symlink():
        retire(tmp)
    try:
        rep = project(live, tmp, recent_n)
        tmp.replace(reach)
    except SkipChat:
        if tmp.exists() or tmp.is_symlink():
            retire(tmp)
        raise
    except Exception as e:
        if tmp.exists() or tmp.is_symlink():
            retire(tmp)
        die(f"prep project failed ({chat.name}): {record_exception('prep.project', e)}")
    if lock_pids(chat, fresh=True):
        _discard_reach(chat)
        die(f"REFUSE prep: re-locked during project pids={lock_pids(chat, fresh=True)} — discarded")
    drifted = snap.drifted()
    live_root_now = root_of(live)
    coherent = (not drifted) and bool(live_root_now) and live_root_now == root_of(reach)
    write_reach_meta(chat, source_root=live_root_now or snap.root,
                     snap=FileSnap.take(live, with_root=True), coherent=coherent)
    against = live if coherent else None
    try:
        fz = falsify(reach, against=against, recent_n=recent_n)
        sm = smoke(reach)
    except Exception as e:
        die(f"prep gates failed ({chat.name}): {record_exception('prep.gates', e)}")
    if not fz["ok"] or not sm["ok"]:
        die(f"cursor gates failed {fz.get('alarms')} {sm.get('errors')}", 3)
    out = dict(kind="cursor", sid=chat.name, cut_mb=rep["mb"], blobs=rep["blobs"],
               drop_n=rep["drop_n"], swapped=False, coherent=coherent,
               drifted=drifted, phase="prep", meta_v=2)
    _mass_bust(live)
    tag = "PREP STALE" if (drifted or not coherent) else "PREP OK"
    print(f"  {tag} {reach.name} {rep['mb']}MB blobs={rep['blobs']} drift={drifted} coh={coherent}")
    return out

def install_cut_sibling(chat: Path, *, prep_out: dict | None = None) -> dict:
    ph = cursor_phase(chat)
    if not ph["allow"]["swap"]:
        die(f"REFUSE install: state={ph['state']} ({ph['why']}) — "
            f"need UNLOCKED_FRESH (quit agent + prep if STALE)")
    live, reach = chat / "store.db", chat / REACH_NAME
    if not reach.exists():
        die("no store.db.reachable to install")
    fresh, why = judge_reach(chat)
    if not fresh:
        die(f"REFUSE install: not fresh ({why})")
    require_unlocked(chat, verb="install")
    lr, rr = root_of(live), root_of(reach)
    if lr and rr and lr == rr:
        live_sz, reach_sz = live.stat().st_size, reach.stat().st_size
        if live_sz <= max(reach_sz * 1.05, reach_sz + 1_000_000):
            print(f"  INSTALL NOOP live={live_sz/1e6:.1f}MB")

            _discard_reach(chat)
            write_settled(chat, FileSnap.take(live, with_root=True), source_root=lr)
            _mass_bust(live)
            return dict(prep_out or {}, kind="cursor", sid=chat.name, swapped=False,
                        phase="install_noop", live_mb=round(live_sz / 1e6, 2),
                        cut_mb=round(reach_sz / 1e6, 2), sibling_retained_mb=0.0,
                        disk_delta_mb=0.0)
    trans = find_transcript(chat.name)
    th0 = shasum(trans) if trans and trans.exists() else None
    live_before_vac = FileSnap.take(live, with_root=True)
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    staged = chat / f"store.db.new-{ts}"
    if staged.exists() or staged.is_symlink():
        retire(staged)
    try: subprocess.check_call(["sqlite3", str(reach), f"VACUUM INTO '{staged}'"])
    except Exception: shutil.copy2(reach, staged)
    if live_before_vac.drifted():
        if staged.exists() or staged.is_symlink():
            retire(staged)
        die("REFUSE install: live mutated during VACUUM — re-prep")
    if lock_pids(chat, fresh=True):
        if staged.exists() or staged.is_symlink():
            retire(staged)
        die(f"re-locked before install pids={lock_pids(chat, fresh=True)}")
    bloated = chat / f"store.db.bloated-{ts}"
    live.rename(bloated)
    try: staged.rename(live)
    except Exception:
        bloated.rename(live); die("install failed — restored")
    for side in (chat / "store.db-wal", chat / "store.db-shm"):
        if side.exists() or side.is_symlink():
            retire(side)
    if not smoke(live)["ok"]:
        live.rename(chat / f"store.db.failed-{ts}"); bloated.rename(live); die("post-install smoke — restored")
    if th0 and trans and shasum(trans) != th0: die("transcript changed")
    cut_mb = round(live.stat().st_size / 1e6, 2)
    bloated_mb = round(bloated.stat().st_size / 1e6, 2)
    _discard_reach(chat)
    write_settled(chat, FileSnap.take(live, with_root=True), source_root=root_of(live))
    _mass_bust(live)
    out = dict(prep_out or {}, kind="cursor", sid=chat.name, swapped=True, phase="install",
               live_mb=cut_mb, bloated=bloated.name,
               cut_mb=cut_mb,
               sibling_retained_mb=bloated_mb,
               disk_delta_mb=round(bloated_mb - cut_mb, 2))
    print(f"  INSTALL OK live={out['live_mb']}MB bloated={out['sibling_retained_mb']}MB ({bloated.name})")
    return out

def _backup(p: Path) -> Path:
    ts = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
    bak = p.with_suffix(p.suffix + f".pretrim-{ts}")
    try: os.link(p, bak)
    except OSError: shutil.copy2(p, bak)
    return bak

def _has_type(raw, name):
    if isinstance(raw, str):
        raw = raw.encode()
    return (f'"type":"{name}"'.encode() in raw) or (f'"type": "{name}"'.encode() in raw)

def _nl(line):
    return line if line.endswith(b"\n") else line + b"\n"

def _codex_is_ui_event(line):
    types = _JSON_TYPE_RE.findall(line)
    if b"event_msg" not in types:
        return False
    for t in types:
        if t.decode("ascii", "ignore") in CODEX_UI_TYPES:
            return True
    return False

def _cap_text(s: str, cap: int) -> tuple[str, bool]:
    if not isinstance(s, str) or len(s) <= cap:
        return s, False
    half = max(64, cap // 2)
    mid = len(s) - 2 * half
    return f"{s[:half]}\n…[trim elided {mid} chars]…\n{s[-half:]}", True

def _cap_jsonish(val, cap: int) -> tuple[object, bool]:
    if isinstance(val, str):
        return _cap_text(val, cap)
    if isinstance(val, list):
        changed = False
        CAP_OUT.clear()
        for x in val:
            if isinstance(x, dict) and isinstance(x.get("text"), str):
                t, c = _cap_text(x["text"], cap)
                y = dict(x); y["text"] = t
                CAP_OUT.append(y); changed |= c
            elif isinstance(x, str):
                t, c = _cap_text(x, cap); CAP_OUT.append(t); changed |= c
            else:
                CAP_OUT.append(x)
        return list(CAP_OUT), changed
    if val is None:
        return val, False
    raw = json.dumps(val, separators=(",", ":"))
    if len(raw) <= cap:
        return val, False
    t, _ = _cap_text(raw, cap)
    return t, True

def _codex_stats_reset() -> None:
    CODEX_STATS.clear()
    CODEX_STATS.update(ui=0, world_state=0, tools=0, reasoning=0)

def _codex_mutate_item(it: dict, *, tools: bool, reasoning: bool, cap: int) -> tuple[dict | None, str]:
    if not isinstance(it, dict):
        return it, ""
    t = it.get("type")
    if reasoning and t == "reasoning":
        return None, "drop_reasoning"
    if tools and t in ("function_call_output", "custom_tool_call_output"):
        out = dict(it)
        new_o, ch = _cap_jsonish(out.get("output"), cap)
        if ch:
            out["output"] = new_o
            return out, "cap_tool"
        return out, ""
    return it, ""

def _codex_force_tail(tail, *, tools, reasoning, cap):
    CODEX_KEEP.clear()
    _codex_stats_reset()
    for line in tail.split(b"\n"):
        if not line.strip():
            continue
        if _codex_is_ui_event(line):
            CODEX_STATS["ui"] += 1; continue
        if _has_type(line[:100], "world_state"):
            CODEX_STATS["world_state"] += 1; continue
        need = tools or reasoning or b"replacement_history" in line
        if not need:
            CODEX_KEEP.extend(_nl(line)); continue
        try:
            o = json.loads(line)
        except Exception:
            bump_coarse("codex_tail_json_skip")
            CODEX_KEEP.extend(_nl(line)); continue
        changed = False
        if o.get("type") == "response_item":
            pl = o.get("payload")
            if isinstance(pl, dict):
                new_pl, act = _codex_mutate_item(pl, tools=tools, reasoning=reasoning, cap=cap)
                if act == "drop_reasoning":
                    CODEX_STATS["reasoning"] += 1; continue
                if act == "cap_tool":
                    o = dict(o); o["payload"] = new_pl; changed = True; CODEX_STATS["tools"] += 1
        elif o.get("type") == "compacted":
            pl = o.get("payload") or {}
            rh = pl.get("replacement_history")
            if isinstance(rh, list) and (tools or reasoning):
                CODEX_RH.clear()
                for it in rh:
                    if not isinstance(it, dict):
                        CODEX_RH.append(it); continue
                    nit, act = _codex_mutate_item(it, tools=tools, reasoning=reasoning, cap=cap)
                    if act == "drop_reasoning":
                        CODEX_STATS["reasoning"] += 1; continue
                    if act == "cap_tool":
                        CODEX_STATS["tools"] += 1
                    CODEX_RH.append(nit if nit is not None else it)
                if CODEX_RH != rh:
                    o = dict(o); pl = dict(pl); pl["replacement_history"] = list(CODEX_RH); o["payload"] = pl
                    changed = True
        if changed:
            line = json.dumps(o, separators=(",", ":")).encode()
        CODEX_KEEP.extend(_nl(line))
    return bytes(CODEX_KEEP), CODEX_STATS

def _codex_align_byte_tail(tail):
    CODEX_ALIGN_LINES.clear()
    for ln in tail.split(b"\n"):
        if ln.strip():
            CODEX_ALIGN_LINES.append(ln)
    if not CODEX_ALIGN_LINES:
        return tail
    start = 0
    for i, line in enumerate(CODEX_ALIGN_LINES):
        if (_has_type(line[:160], "event_msg") and b"user_message" in line) or (
            _has_type(line[:160], "response_item") and (b'"role":"user"' in line or b'"role": "user"' in line)
        ):
            start = i; break
    else:
        for i, line in enumerate(CODEX_ALIGN_LINES):
            if b"function_call_output" in line or b"custom_tool_call_output" in line:
                continue
            start = i; break
    CODEX_ALIGN_SEEN.clear()
    CODEX_ALIGN_KEPT.clear()
    for line in CODEX_ALIGN_LINES[start:]:
        m = re.search(br'"call_id"\s*:\s*"([^"]+)"', line)
        cid = m.group(1) if m else None
        if b"function_call" in line and b"function_call_output" not in line and b"custom_tool_call_output" not in line:
            if cid: CODEX_ALIGN_SEEN.add(cid)
            CODEX_ALIGN_KEPT.append(line); continue
        if b"function_call_output" in line or b"custom_tool_call_output" in line:
            if cid and cid not in CODEX_ALIGN_SEEN:
                continue
            CODEX_ALIGN_KEPT.append(line); continue
        CODEX_ALIGN_KEPT.append(line)
    return b"".join(_nl(ln) for ln in CODEX_ALIGN_KEPT)

def trim_codex_jsonl(path, keep_mb, elide_ui=True, elide_tools=False, elide_reasoning=False,
                     tool_cap=DEFAULT_TOOL_CAP):
    if is_locked(path): die(f"LOCKED {path.name}")
    sz = path.stat().st_size
    force = elide_ui or elide_tools or elide_reasoning
    if sz <= int(keep_mb * 1_000_000) + 64_000 and not force:
        return dict(kind="codex", path=str(path), skipped=True, reason="already small", mb=round(sz / 1e6, 2))
    bak = _backup(path)
    CODEX_HEAD.clear()
    last_c = -1
    with open(path, "rb") as f:
        while True:
            off = f.tell(); line = f.readline()
            if not line: break
            raw = line.strip()
            if not raw: continue
            if _has_type(raw[:100], "session_meta") or (
                _has_type(raw[:100], "turn_context") and len(CODEX_HEAD) < 6 and off < 256_000
            ):
                CODEX_HEAD.append(_nl(line))
            if _has_type(raw[:100], "compacted") and b"replacement_history" in raw:
                last_c = off
        mode = "checkpoint"
        if last_c < 0:
            mode = "byte-tail"
            f.seek(max(0, sz - int(keep_mb * 1_000_000)))
            if f.tell() > 0: f.readline()
            tail = _codex_align_byte_tail(f.read())
        else:
            f.seek(last_c); tail = f.read()
    _codex_stats_reset()
    if force:
        tail, _ = _codex_force_tail(tail, tools=elide_tools, reasoning=elide_reasoning, cap=tool_cap)
        bits = [f"{k}({CODEX_STATS[k]})" for k in ("ui", "world_state", "tools", "reasoning") if CODEX_STATS[k]]
        if bits:
            mode = mode + "+" + "+".join(bits)
    warn = json.dumps({
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "type": "event_msg",
        "payload": {"type": "warning", "message": f"trim seam mode={mode}"},
    }).encode() + b"\n"
    tmp = path.with_suffix(".jsonl.trimming")
    tmp.write_bytes(b"".join(CODEX_HEAD) + warn + tail)
    first = tmp.read_bytes().split(b"\n", 1)[0]
    try:
        if json.loads(first).get("type") != "session_meta":
            retire(tmp); die("codex trim lost session_meta head")
    except Exception:
        retire(tmp); die("codex trim head not JSON")
    tmp.replace(path)

    if CODEX_STATS["ui"]:
        bump_coarse("codex_ui_dropped", CODEX_STATS["ui"])
    if CODEX_STATS["world_state"]:
        bump_coarse("codex_world_state_dropped", CODEX_STATS["world_state"])
    if CODEX_STATS["reasoning"]:
        bump_coarse("codex_reasoning_dropped", CODEX_STATS["reasoning"])
    if CODEX_STATS["tools"]:
        bump_coarse("codex_tools_capped", CODEX_STATS["tools"])
    return dict(kind="codex", sid=path.name, before_mb=round(sz / 1e6, 2),
                after_mb=round(path.stat().st_size / 1e6, 2), backup=str(bak), mode=mode,
                ui_dropped=CODEX_STATS["ui"], world_state_dropped=CODEX_STATS["world_state"],
                tools_capped=CODEX_STATS["tools"], reasoning_dropped=CODEX_STATS["reasoning"],
                tool_cap=tool_cap)

def _claude_slim_message(o: dict, elide_thinking: bool, elide_tools: bool = False,
                         tool_cap: int = DEFAULT_TOOL_CAP) -> dict:
    o = dict(o)
    if "toolUseResult" in o and o.get("type") == "user":
        content = (o.get("message") or {}).get("content")
        if isinstance(content, list) and any(isinstance(b, dict) and b.get("type") == "tool_result" for b in content):
            o.pop("toolUseResult", None)
    if o.get("type") == "user" and elide_tools:
        msg = o.get("message")
        if isinstance(msg, dict) and isinstance(msg.get("content"), list):
            msg = dict(msg); new_c = []; any_cap = False
            for b in msg["content"]:
                if isinstance(b, dict) and b.get("type") == "tool_result":
                    b = dict(b)
                    new_v, ch = _cap_jsonish(b.get("content"), tool_cap)
                    if ch:
                        b["content"] = new_v; any_cap = True
                new_c.append(b)
            if any_cap:
                msg["content"] = new_c; o["message"] = msg
    if elide_thinking and o.get("type") == "assistant":
        msg = o.get("message")
        if isinstance(msg, dict) and isinstance(msg.get("content"), list):
            msg = dict(msg)
            msg["content"] = [b for b in msg["content"]
                              if not (isinstance(b, dict) and b.get("type") == "thinking")]
            o["message"] = msg
    return o

def trim_claude_jsonl(path, keep_turns, elide_ui=True, elide_thinking=False, elide_tools=False,
                      tool_cap=DEFAULT_TOOL_CAP):
    if is_locked(path): die(f"LOCKED {path.name}")
    sz = path.stat().st_size
    recs = []
    with open(path, "rb") as f:
        while True:
            off = f.tell(); line = f.readline()
            if not line: break
            if not line.strip(): continue
            try: recs.append((off, json.loads(line)))
            except Exception: continue
    ua = [(off, o) for off, o in recs if o.get("type") in ("user", "assistant") and o.get("uuid")]
    if len(ua) <= keep_turns + 5:
        return dict(kind="claude", path=str(path), skipped=True, reason="few turns",
                    turns=len(ua), mb=round(sz / 1e6, 2))
    by_id = {o["uuid"]: (o.get("parentUuid"), off) for off, o in ua}
    tip = ua[-1][1]["uuid"]
    keep_ids = {o["uuid"] for _, o in ua[-keep_turns:]}
    chain, cur = [], tip
    while cur and cur in by_id and len(chain) < keep_turns:
        chain.append(cur); keep_ids.add(cur); cur = by_id[cur][0]
    if not chain:
        die("claude tip-chain empty")
    use_at, res_at = {}, {}
    for off, o in recs:
        msg = (o.get("message") or {}).get("content") or []
        if o.get("type") == "assistant" and o.get("uuid"):
            for b in msg:
                if isinstance(b, dict) and b.get("type") == "tool_use" and b.get("id"):
                    use_at[b["id"]] = o["uuid"]
        if o.get("type") == "user" and o.get("uuid"):
            for b in msg:
                if isinstance(b, dict) and b.get("type") == "tool_result" and b.get("tool_use_id"):
                    res_at[b["tool_use_id"]] = o["uuid"]
            if o.get("sourceToolUseID"):
                res_at[o["sourceToolUseID"]] = o["uuid"]
    changed = True
    while changed:
        changed = False
        for tid, au in use_at.items():
            ru = res_at.get(tid)
            if au in keep_ids and ru and ru not in keep_ids and ru in by_id:
                keep_ids.add(ru); changed = True
            if ru in keep_ids and au not in keep_ids and au in by_id:
                keep_ids.add(au); changed = True
    ordered = [o["uuid"] for _, o in ua if o["uuid"] in keep_ids]
    chain_root = ordered[0] if ordered else chain[-1]
    preamble = []
    for off, o in recs:
        if o.get("type") in ("user", "assistant"): break
        if o.get("subtype") == "compact_boundary" or o.get("type") in CLAUDE_DROP_TYPES:
            continue
        if o.get("type") in ("mode", "permission-mode") or (not elide_ui and o.get("type") in CLAUDE_PREAMBLE):
            preamble.append(off)
    keep_offs = set(preamble) | {by_id[u][1] for u in keep_ids if u in by_id}
    root_off = by_id[chain_root][1]
    tip_o = ua[-1][1]
    boundary = str(uuid.uuid4())
    bak = _backup(path)
    tmp = path.with_suffix(".jsonl.trimming")
    with open(path, "rb") as srcf, open(tmp, "wb") as dst:
        wrote = False
        while True:
            off = srcf.tell(); line = srcf.readline()
            if not line: break
            if off not in keep_offs: continue
            if not wrote and off == root_off:
                seam = {k: tip_o.get(k) for k in
                        ("sessionId", "timestamp", "cwd", "version", "gitBranch", "entrypoint", "slug", "userType")}
                seam.update(
                    type="system", subtype="compact_boundary", uuid=boundary, parentUuid=None,
                    logicalParentUuid=chain_root, isSidechain=False, isMeta=False, level="info",
                    content="Conversation compacted",
                    sessionId=seam.get("sessionId") or path.stem,
                    timestamp=seam.get("timestamp") or time.strftime("%Y-%m-%dT%H:%M:%S.000Z", time.gmtime()),
                    userType=seam.get("userType") or "external",
                    compactMetadata={
                        "trigger": "trim",
                        "preservedSegment": {"headUuid": chain_root, "anchorUuid": chain_root, "tailUuid": tip},
                        "preservedMessages": {
                            "anchorUuid": chain_root,
                            "uuids": list(reversed(chain))[:16],
                            "allUuids": list(keep_ids)[:64],
                        },
                    },
                )
                dst.write(json.dumps({k: v for k, v in seam.items() if v is not None},
                                     separators=(",", ":")).encode() + b"\n")
                wrote = True
            try:
                o = json.loads(line)
            except Exception:
                dst.write(line); continue
            if o.get("type") in ("user", "assistant"):
                o = _claude_slim_message(o, elide_thinking, elide_tools, tool_cap)
                pu = o.get("parentUuid")
                if o.get("uuid") == chain_root or (pu and pu not in keep_ids and pu != boundary):
                    o["parentUuid"] = boundary
                line = json.dumps(o, separators=(",", ":")).encode() + b"\n"
            dst.write(line if line.endswith(b"\n") else line + b"\n")
    if tmp.stat().st_size < 100:
        retire(tmp); die("claude trim produced empty file")
    tmp.replace(path)
    return dict(kind="claude", sid=path.stem, before_mb=round(sz / 1e6, 2),
                after_mb=round(path.stat().st_size / 1e6, 2), kept=len(keep_ids),
                backup=str(bak), boundary=boundary, chain=len(chain),
                elide_ui=elide_ui, elide_thinking=elide_thinking,
                elide_tools=elide_tools, tool_cap=tool_cap)

def _cut_cursor(s: Sess, cut: Cut, *, swap: bool = False) -> dict:
    held = lock_pids(s.path)
    s.scan_saw_lock = bool(held)
    chat = s.path.parent
    if swap:
        if held:
            return dict(kind="cursor", sid=s.sid, skipped="locked", pids=held)
        if not cursor_phase(chat)["allow"]["swap"]:
            prep_cut_sibling(chat, cut.recent)
        return install_cut_sibling(chat)
    return prep_cut_sibling(chat, cut.recent)

def _cut_codex(s: Sess, cut: Cut, *, swap: bool = False) -> dict:
    held = lock_pids(s.path)
    s.scan_saw_lock = bool(held)
    if held:
        return dict(kind="codex", sid=s.sid, skipped="locked", pids=held)
    rep = trim_codex_jsonl(s.path, cut.keep_mb, elide_tools=cut.tools,
                           elide_reasoning=cut.reasoning, tool_cap=cut.tool_cap)
    if not s.path.exists():
        rep["error"] = "path_vanished_during_trim"
    return rep

def _cut_claude(s: Sess, cut: Cut, *, swap: bool = False) -> dict:
    held = lock_pids(s.path)
    s.scan_saw_lock = bool(held)
    if held:
        return dict(kind="claude", sid=s.sid, skipped="locked", pids=held)
    return trim_claude_jsonl(s.path, cut.turns, elide_thinking=cut.thinking,
                             elide_tools=cut.tools, tool_cap=cut.tool_cap)

def trim_session(s: Sess, cut: Cut, *, swap: bool = False) -> dict:
    d = KIND.get(s.kind)
    if d is None:
        return dict(kind=s.kind, sid=s.sid, error=f"unknown kind {s.kind}")
    return d.cut(s, cut, swap=swap)

def _verify_codex(s: Sess) -> list[str]:
    errs: list[str] = []
    first = json.loads(s.path.read_bytes().split(b"\n", 1)[0])
    if first.get("type") != "session_meta":
        errs.append("codex head not session_meta")
    return errs

def _verify_claude(s: Sess) -> list[str]:
    errs: list[str] = []
    lines = []
    with open(s.path, "rb") as f:
        for line in f:
            if not line.strip():
                continue
            try:
                lines.append(json.loads(line))
            except Exception:
                continue
    ids = {o["uuid"] for o in lines if o.get("uuid")}
    miss = sum(1 for o in lines if o.get("type") in ("user", "assistant")
               and o.get("parentUuid") and o["parentUuid"] not in ids)
    cbs = sum(1 for o in lines if o.get("subtype") == "compact_boundary")
    if miss:
        errs.append(f"claude miss_parent={miss}")
    if cbs != 1:
        errs.append(f"claude cbs={cbs}")
    return errs

def _verify_cursor(s: Sess) -> list[str]:
    errs: list[str] = []
    reach = s.path.parent / "store.db.reachable"
    target = reach if reach.exists() else s.path
    if not is_locked(target):
        sm = smoke(target)
        if not sm.get("ok"):
            errs.append(f"cursor smoke {sm.get('errors')}")
    return errs

def verify_cut(s: Sess) -> list[str]:
    d = KIND.get(s.kind)
    if d is None:
        return [f"unknown kind {s.kind}"]
    try:
        return d.verify(s)
    except Exception as e:
        return [f"verify-exc:{e}"]

KindDriver = namedtuple("KindDriver", "scan enrich cut verify")

def _install_kinds() -> None:
    """One table owns kind behavior — new harness = register, not elif."""
    KIND.clear()
    KIND["cursor"] = KindDriver(_scan_cursor_window, _enrich_cursor, _cut_cursor, _verify_cursor)
    KIND["codex"] = KindDriver(_scan_codex_window, _enrich_codex, _cut_codex, _verify_codex)
    KIND["claude"] = KindDriver(_scan_claude_window, _enrich_claude, _cut_claude, _verify_claude)

_install_kinds()

def apply_cuts(sessions: list[Sess], cut: Cut, *, swap: bool = False,
               verify: bool = False) -> list[dict]:
    out: list[dict] = []
    for s in sessions:
        s.scan_saw_lock = is_locked(s.path)
        print(f"\n→ {s.kind} {s.sid[:12]} ({s.mb:.1f}MB){' LOCK ' + str(lock_pids(s.path)) if s.locked else ''}")
        try:
            r = trim_session(s, cut, swap=swap)
            out.append(r)
            if r.get("skipped"):
                print(f"  SKIP {r['skipped']} — quit app, re-run"); continue
            if r.get("error"):
                print(f"  FAIL {r['error']}"); continue
            if "before_mb" in r and "after_mb" in r:
                extra = r.get("mode") or (f"kept={r['kept']}" if "kept" in r else "")
                bak = r.get("backup") or ""
                bak_mb = 0.0
                if bak:
                    bp = s.path.parent / bak if not Path(bak).is_absolute() else Path(bak)
                    if not bp.exists() and r.get("backup"):
                        bp = Path(r["backup"])
                    try: bak_mb = bp.stat().st_size / 1e6
                    except OSError: bak_mb = float(r["before_mb"])
                logical = round(r["before_mb"] - r["after_mb"], 2)
                disk = round(logical - bak_mb, 2)
                r["logical_delta_mb"] = logical
                r["sibling_retained_mb"] = round(bak_mb, 2)
                r["disk_delta_mb"] = disk
                print(f"  {r['before_mb']}→{r['after_mb']} MB  logical=-{logical} "
                      f"sibling_retained={bak_mb:.1f} disk≈{disk:+.1f}  {extra}")
                if bak:
                    print(f"  bak={bak}")
            else:
                print(f"  {r}")
            if verify and not r.get("skipped"):
                verrs = verify_cut(s)
                r["verify"] = verrs
                if verrs:
                    print(f"  VERIFY FAIL {verrs}")
                else:
                    print("  VERIFY OK")
        except SystemExit:
            raise
        except Exception as e:
            print(f"  FAIL {e}")
            out.append(dict(error=str(e), sid=s.sid, kind=s.kind))
    return out

def retire_siblings(chat: Path) -> dict:
    """Trash non-undo siblings only. bloated/pretrim stay for restore."""
    removed = 0; freed = 0; skipped = 0; kept_undo = 0
    for p in list_sibling_paths(chat):
        if is_cut_undo(p):
            kept_undo += 1
            continue
        if lock_pids(p):
            skipped += 1
            continue
        try:
            sz = retire(p)
            if sz:
                removed += 1
                freed += sz
        except OSError:
            skipped += 1
    return dict(removed=removed, freed_mb=round(freed / 1e6, 2),
                skipped=skipped, kept_undo=kept_undo, dest="Trash")

def drop_bound_siblings(chat: Path, **_kw) -> dict:
    """Deprecated name → retire_siblings (undo always kept)."""
    return retire_siblings(chat)

def settle_chat(chat: Path, recent_n: int = DEFAULT_RECENT, *, quiet: bool = False) -> dict:
    before = cursor_phase(chat)
    SETTLE_ACTIONS.clear()
    if not quiet:
        print(f"SETTLE bound={before['disk_bound_mb']}MB  state={before['state']} "
              f"kind={before.get('kind')} ({before['why']})")

    if before["allow"]["prep"]:
        try:
            SETTLE_ACTIONS.append(("prep", prep_cut_sibling(chat, recent_n)))
        except SkipChat as e:
            SETTLE_ACTIONS.append(("prep_skip", dict(why=e.why)))
            if not quiet:
                print(f"  prep_skip {e.why} — not a settle candidate")

    mid = cursor_phase(chat)
    if mid["allow"]["swap"]:
        SETTLE_ACTIONS.append(("install", install_cut_sibling(chat)))
    SETTLE_ACTIONS.append(("siblings", retire_siblings(chat)))

    after = cursor_phase(chat)
    SETTLE_LEDGER.clear()
    SETTLE_LEDGER.update(
        chat=chat.name,
        before=dict(state=before["state"], kind=before.get("kind"), why=before["why"],
                    bound_mb=before["disk_bound_mb"],
                    live_mb=before["live_mb"], sibling_mb=before["sibling_mb"]),
        actions=[{a: r} for a, r in SETTLE_ACTIONS],
        after=dict(state=after["state"], kind=after.get("kind"), why=after["why"],
                   bound_mb=after["disk_bound_mb"],
                   live_mb=after["live_mb"], sibling_mb=after["sibling_mb"]),
        delta_bound_mb=round(before["disk_bound_mb"] - after["disk_bound_mb"], 2),
    )
    if not quiet:
        print(f"LEDGER  bound {SETTLE_LEDGER['before']['bound_mb']}→{SETTLE_LEDGER['after']['bound_mb']} MB  "
              f"Δ={SETTLE_LEDGER['delta_bound_mb']:+}  {before['state']}/{before.get('kind')}→"
              f"{after['state']}/{after.get('kind')}")
        if mid.get("kind") != "SETTLED" and not mid["allow"]["swap"] and lock_pids(chat / "store.db"):
            print(f"  still held — end agent, then settle (prep refused while locked)")
    return dict(SETTLE_LEDGER)

def settle_all_chats(recent_n: int = DEFAULT_RECENT, *, min_bound_mb: float = 5.0) -> list[dict]:
    SETTLE_ALL_CHATS.clear()
    SETTLE_ALL_OUT.clear()
    if not CURSOR_CHATS.exists():
        return SETTLE_ALL_OUT
    _scan_cursor_window()
    for s in STORE_IDX.values():
        if s.kind != "cursor":
            continue
        bound = disk_bound_mb(s.path.parent)
        if bound >= min_bound_mb:
            SETTLE_ALL_CHATS.append((bound, s.path.parent))
    SETTLE_ALL_CHATS.sort(reverse=True)
    print(f"SETTLE-ALL {len(SETTLE_ALL_CHATS)} chats bound≥{min_bound_mb}MB")
    for bound, chat in SETTLE_ALL_CHATS:
        try:
            print(f"\n→ {chat.name[:36]} bound={bound:.1f}MB")
            SETTLE_ALL_OUT.append(settle_chat(chat, recent_n))
        except SystemExit as e:
            SETTLE_ALL_OUT.append(dict(chat=chat.name, skipped=True, code=e.code))
            print(f"  SKIP exit={e.code}")
        except Exception as e:
            lab = record_exception("settle_all", e)
            SETTLE_ALL_OUT.append(dict(chat=chat.name, error=lab, exc_sidecar=dict(LAST_EXC)))
            print(f"  FAIL {lab}")
    delta = sum(x.get("delta_bound_mb", 0) for x in SETTLE_ALL_OUT
                if isinstance(x.get("delta_bound_mb"), (int, float)))
    skipped = sum(1 for x in SETTLE_ALL_OUT if x.get("skipped"))
    print(f"\nSETTLE-ALL done  n={len(SETTLE_ALL_OUT)} skipped={skipped}  ΣΔbound={delta:+.1f}MB")
    return SETTLE_ALL_OUT

def graph_reset() -> None:
    global GRAPH_HEAD, GRAPH_BYTES
    GRAPH_ORDER.clear()
    GRAPH_QUEUED.clear()
    GRAPH_TAG.clear()
    GRAPH_HEAD = 0
    GRAPH_BYTES = 0

def _graph_enqueue(hid: str, tag: str = "?") -> None:
    if not hid or hid in GRAPH_QUEUED:
        return
    GRAPH_QUEUED.add(hid)
    GRAPH_ORDER.append(hid)
    GRAPH_TAG[hid] = tag

def _graph_is_terminal(hid: str, snap: Snap) -> bool:
    tag = GRAPH_TAG.get(hid, "?")
    if tag in GRAPH_TERMINAL_TAGS:
        return True
    ln = snap.length(hid) or 0
    if tag == "step":
        return ln > GRAPH_STEP_EXPAND_MAX
    if tag == "root:f3":
        return ln > GRAPH_F3_EXPAND_MAX
    return False

def _graph_expand_blob(data: bytes) -> None:
    """One fields() pass ≡ turn_edges + declare_root enqueue (plan_* still use those)."""
    for f, wt, val in fields(data):
        if wt != 2 or val is None:
            continue
        if f == 1:
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ev is not None:
                    if ef == 1:
                        _graph_enqueue(as_id(ev) or "", "user_message")
                    elif ef == 2:
                        _graph_enqueue(as_id(ev) or "", "step")
        elif f == 2:
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ev is not None:
                    if ef == 1:
                        _graph_enqueue(as_id(ev) or "", "shell_command")
                    elif ef == 2:
                        _graph_enqueue(as_id(ev) or "", "shell_output")
        if f in (12, 31):
            for ef, ewt, ev in fields(val):
                if ewt == 2 and ef == 2 and (hid := as_id(ev)):
                    _graph_enqueue(hid, "root:map" + str(f))
                    _graph_enqueue(hid, "map")
            continue
        hid = as_id(val)
        if not hid:
            continue
        law = ROOT_LAW.get(f)
        if f == 8:
            _graph_enqueue(hid, "root:f8")
            _graph_enqueue(hid, "turn")
        elif law == "MAP":
            continue
        elif law in ("MUST", "SEAL") or law is None:
            _graph_enqueue(hid, "root:f" + str(f))

def codec_graph(snap: Snap) -> tuple[int, int]:
    global GRAPH_BYTES, GRAPH_HEAD
    graph_reset()
    _graph_enqueue(snap.tip(), "tip")
    while GRAPH_HEAD < len(GRAPH_ORDER):
        hid = GRAPH_ORDER[GRAPH_HEAD]
        GRAPH_HEAD += 1
        if _graph_is_terminal(hid, snap):
            INSTR["graph_terminal_skip"] += 1
            continue
        data = snap.get(hid)
        if not data:
            continue
        INSTR["graph_expand"] += 1
        try:
            _graph_expand_blob(data)
        except Exception as e:
            record_exception("codec_graph.expand", e)
            bump_coarse("codec_graph_expand_skip")
            continue
    GRAPH_BYTES = sum(snap.length(h) or 0 for h in GRAPH_QUEUED)
    return len(GRAPH_QUEUED), GRAPH_BYTES

def _mass_disk_path() -> Path:
    return CURSOR_HOME / "trim_mass_cache.json"

def _mass_disk_load() -> None:
    global _MASS_DISK_LOADED
    with _MASS_LOCK:
        if _MASS_DISK_LOADED:
            return
    p = _mass_disk_path()
    if not p.exists():
        with _MASS_LOCK:
            if not _MASS_DISK_LOADED:
                _MASS_DISK_LOADED = True
                INSTR["mass_disk_absent"] += 1
        return
    try:
        data = json.loads(p.read_text())
    except Exception:
        with _MASS_LOCK:
            if not _MASS_DISK_LOADED:
                _MASS_DISK_LOADED = True
                INSTR["mass_disk_bad"] += 1
        return
    with _MASS_LOCK:
        if _MASS_DISK_LOADED:
            return
        n = 0
        for k, v in data.items():
            if isinstance(v, list) and len(v) == 4:
                _MASS_CACHE[k] = (int(v[0]), int(v[1]), v[2], v[3])
                n += 1
        _MASS_DISK_LOADED = True
        INSTR["mass_disk_load"] += n

def _mass_disk_save() -> None:
    global _MASS_DISK_DIRTY
    with _MASS_LOCK:
        if not _MASS_DISK_DIRTY:
            return
        payload = {k: [a, b, c, d] for k, (a, b, c, d) in _MASS_CACHE.items()}
        _MASS_DISK_DIRTY = False
    p = _mass_disk_path()
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(payload, separators=(",", ":")))
        tmp.replace(p)
        INSTR["mass_disk_save"] += 1
    except Exception:
        with _MASS_LOCK:
            _MASS_DISK_DIRTY = True
        INSTR["mass_disk_save_fail"] += 1

def _mass_key(live: Path) -> str:
    try:
        return str(live.resolve())
    except OSError:
        return str(live)

def _mass_bust(*lives: Path) -> None:
    global _MASS_DISK_DIRTY
    with _MASS_LOCK:
        for p in lives:
            for key in {_mass_key(p), str(p)}:
                if key in _MASS_CACHE:
                    _MASS_CACHE.pop(key, None)
                    _MASS_DISK_DIRTY = True
                    INSTR["mass_bust"] += 1

def _mass_fp(live: Path) -> tuple[int, int, str | None] | None:
    try:
        st = live.stat()
    except OSError:
        return None
    return st.st_mtime_ns, st.st_size, root_of(live)

def _mass_lookup(live: Path) -> dict | None:
    _mass_disk_load()
    fp = _mass_fp(live)
    if fp is None:
        return None
    mtime_ns, size, root = fp
    key = _mass_key(live)
    with _MASS_LOCK:
        hit = _MASS_CACHE.get(key)
        if hit is not None and hit[0] == mtime_ns and hit[1] == size and hit[2] == root:
            INSTR["mass_hit"] += 1
            return dict(hit[3]) if isinstance(hit[3], dict) else None
        INSTR["mass_miss"] += 1
    return None

def _mass_put(live: Path, mass: dict) -> None:
    global _MASS_DISK_DIRTY
    fp = _mass_fp(live)
    if fp is None or mass.get("graph_mb") is None:
        return
    compact = {k: mass.get(k) for k in _MASS_COMPACT_KEYS}
    with _MASS_LOCK:
        _MASS_CACHE[_mass_key(live)] = (fp[0], fp[1], fp[2], compact)
        _MASS_DISK_DIRTY = True

def store_mass(chat: Path) -> dict:
    MASS.clear()
    MASS.update(file_mb=0.0, payload_mb=0.0, n_blobs=0, graph_mb=None,
                out_of_graph_mb=None, plan_keep_mb=None, admit_drop_mb=None,
                turns=None, n_graph=None, skip=None, admit_buckets=None,
                exc_sidecar=None, mass_cached=False)
    live = chat / "store.db" if chat.is_dir() else chat
    if not live.exists():
        MASS["skip"] = "no_live"; return dict(MASS)
    cached = _mass_lookup(live)
    if cached is not None:
        MASS.update(cached)
        MASS["mass_cached"] = True
        if isinstance(cached.get("admit_buckets"), dict):
            ADMIT_BUCKETS.clear()
            ADMIT_BUCKETS.update(cached["admit_buckets"])
        bump_coarse("mass_cache_hit")
        return dict(MASS)
    MASS["file_mb"] = round(live.stat().st_size / 1e6, 2)
    try:
        con = open_ro(live)
        MASS["n_blobs"] = con.execute("SELECT COUNT(*) FROM blobs").fetchone()[0]
        payload = con.execute("SELECT SUM(LENGTH(data)) FROM blobs").fetchone()[0] or 0
        con.close()
        MASS["payload_mb"] = round(payload / 1e6, 2)
    except Exception as e:
        MASS["skip"] = record_exception("store_mass.ro", e)
        MASS["exc_sidecar"] = dict(LAST_EXC)
        return dict(MASS)
    try:
        with Snap(live) as s:

            n_graph, gbytes = codec_graph(s)
            plan = plan_from(s, DEFAULT_RECENT)
        MASS["n_graph"] = n_graph
        MASS["graph_mb"] = round(gbytes / 1e6, 2)
        MASS["out_of_graph_mb"] = round(max(0.0, MASS["payload_mb"] - MASS["graph_mb"]), 2)
        MASS["plan_keep_mb"] = round(plan.bytes_est / 1e6, 2)
        MASS["admit_drop_mb"] = round(max(0.0, MASS["graph_mb"] - MASS["plan_keep_mb"]), 2)
        MASS["turns"] = len(plan.turns)
        MASS["admit_buckets"] = dict(ADMIT_BUCKETS)
        _mass_put(live, MASS)
        bump_coarse("mass_ok")
        for k, v in ADMIT_BUCKETS.items():
            if not k.startswith("tag:"):
                bump_coarse(f"admit:{k}", v)
    except SkipChat as e:
        MASS["skip"] = e.why
        bump_coarse(f"skip:{e.why.split(':', 1)[0]}")
    except Exception as e:
        MASS["skip"] = record_exception("store_mass.plan", e)
        MASS["exc_sidecar"] = dict(LAST_EXC)
    return dict(MASS)

def cmd_status(chat):
    ph = cursor_phase(chat)
    a = ph["allow"]
    now = []
    if a["prep"] and not judge_reach(chat)[0]: now.append("prep")
    if a["isolate"]: now.append("isolate")
    if a["swap"]: now.append("install")
    now.append("retire_siblings")  # never cut-undo
    print(f"state {ph['state']} ({ph['why']}) pids={ph['pids'] or '-'}")
    print(f"now {' · '.join(now)}")
    print(f"bound live={ph['live_mb']} + sib={ph['sibling_mb']} = {ph['disk_bound_mb']}MB")
    live, reach = chat / "store.db", chat / REACH_NAME
    lr = root_of(live) if live.exists() else None
    if live.exists():
        con = open_ro(live); n = con.execute("SELECT COUNT(*) FROM blobs").fetchone()[0]; con.close()
        print(f"live {ph['live_mb']}MB / {n}  {(lr or '?')[:16]}")
    if reach.exists():
        rr = root_of(reach)
        con = open_ro(reach); n = con.execute("SELECT COUNT(*) FROM blobs").fetchone()[0]; con.close()
        print(f"reach {round(reach.stat().st_size/1e6,2)}MB / {n}  {(rr or '?')[:16]}")
        if lr and rr and lr != rr:
            print(f"WARN reach root DIVERGED from live — not an install/isolate product")
        meta = read_reach_meta(chat)
        if meta:
            print(f"meta v={meta.get('v')} coh={meta.get('coherent')} ts={meta.get('cut_ts')}")
    mass = store_mass(chat)
    if mass.get("graph_mb") is not None:
        print(f"mass file={mass['file_mb']} payload={mass['payload_mb']} "
              f"graph={mass['graph_mb']} out_of_graph={mass['out_of_graph_mb']} "
              f"plan_keep={mass['plan_keep_mb']} admit_drop={mass['admit_drop_mb']}MB "
              f"turns={mass['turns']}")
        print("  admit_drop = in-graph not kept by recent/admit (NOT garbage); "
              "out_of_graph = outside codec walk")
        ab = mass.get("admit_buckets") or {}
        classes = {k: v for k, v in ab.items() if not k.startswith("tag:")}
        if classes:
            print(f"  admit_buckets {classes}")
        if mass.get("mass_cached"):
            print("  mass_cached hit (amortized; bust on prep/install)")
    elif mass.get("skip"):
        print(f"mass skip={mass['skip']} file={mass['file_mb']} payload={mass['payload_mb']}")
        if mass.get("exc_sidecar"):
            ex = mass["exc_sidecar"]
            print(f"  exc_sidecar {ex.get('site')} {ex.get('typ')}: {ex.get('msg', '')[:120]}")
    _mass_disk_save()
    t = find_transcript(chat.name)
    print(f"transcript {round(t.stat().st_size/1e6,2)}MB" if t and t.exists() else "transcript MISSING")

def cmd_coarse(_=None):
    rep = coarse_report()
    print("COARSE")
    print(f"admit_buckets {rep['admit_buckets'] or '{}'}")
    print(f"coarse_buckets {rep['coarse_buckets'] or '{}'}")
    print(f"exc_sidecar_n {rep['exc_sidecar_n']}")
    if rep["last_exc"]:
        ex = rep["last_exc"]
        print(f"last_exc {ex.get('site')} {ex.get('typ')}: {ex.get('msg', '')[:160]}")
        if ex.get("tb"):
            print("--- tb ---")
            print(ex["tb"][-600:])
    print("evidence_loss:")
    for row in rep["unfalsifiable"]:
        print(f"  compressed_into={row['compressed_into']}")
        print(f"    dropped_detail={row['dropped_detail']}")
        print(f"    unfalsifiable_claim={row['unfalsifiable_claim']}")
    return rep

def cmd_prep(chat, recent_n):
    ph = cursor_phase(chat)
    if not ph["allow"]["prep"]:
        die(f"REFUSE prep: state={ph['state']} ({ph['why']}) pids={ph['pids']}")
    try:
        prep_cut_sibling(chat, recent_n)
    except SkipChat as e:
        die(f"REFUSE prep: {e.why}")

def _pb_varint(x: int) -> bytes:
    PB_VARINT_BUF.clear()
    while True:
        b = x & 0x7F
        x >>= 7
        PB_VARINT_BUF.append(b | (0x80 if x else 0))
        if not x:
            return bytes(PB_VARINT_BUF)

def _pb_ld(f: int, p: bytes) -> bytes:
    return _pb_varint((f << 3) | 2) + _pb_varint(len(p)) + p

def _pb_vid(n: int) -> bytes:
    return hashlib.sha256(f"t{n}".encode()).digest()

def _write_store(path: Path, blobs: dict[str, bytes], root_hex: str, *, name: str = "thin") -> None:
    if path.exists():
        retire(path)
    con = sqlite3.connect(path)
    con.execute("CREATE TABLE blobs(id TEXT PRIMARY KEY, data BLOB)")
    con.execute("CREATE TABLE meta(key TEXT PRIMARY KEY, value TEXT)")
    for k, v in blobs.items():
        con.execute("INSERT INTO blobs VALUES(?,?)", (k, v))
    meta = dict(agentId="thin", latestRootBlobId=root_hex,
                blobEncryptionKey="0" * 64, name=name)
    con.execute("INSERT INTO meta VALUES('0',?)", (json.dumps(meta).encode().hex(),))
    con.commit()
    con.close()

def _synthetic_blobs(*, n_turns: int = MIN_TURNS):
    root, turn, user, step_h, f1h, arch, arch_c = map(_pb_vid, range(7))
    blobs = {
        root.hex(): _pb_ld(8, turn) + _pb_ld(1, f1h) + _pb_ld(13, arch),
        turn.hex(): _pb_ld(1, _pb_ld(1, user) + _pb_ld(2, step_h)),
        user.hex(): b"hi",
        step_h.hex(): b"H" * (MAX_LEAF + 50),
        f1h.hex(): b"P" * (MAX_LEAF + 5000),
        arch.hex(): _pb_ld(1, arch_c),
        arch_c.hex(): b"drop-me",
    }
    extra = b""
    for i in range(n_turns):
        t, u = _pb_vid(100 + i), _pb_vid(200 + i)
        blobs[t.hex()] = _pb_ld(1, _pb_ld(1, u))
        blobs[u.hex()] = f"u{i}".encode()
        extra += _pb_ld(8, t)
    blobs[root.hex()] = extra + blobs[root.hex()]
    ids = dict(root=root.hex(), f1=f1h.hex(), arch=arch.hex(),
               arch_c=arch_c.hex(), step=step_h.hex())
    return blobs, root.hex(), ids

def reliability_battery() -> dict:
    global lock_pids, lock_pids_many, _LOCK_SNAP, CURSOR_PROJS, TX_WIN
    global _file_history_tip_named
    CHECK_FAILS.clear()
    CHECK_INFO.clear()

    def tooth(name: str, cond: bool, detail: str = "") -> None:
        if cond:
            print(f"  OK {name}" + (f" {detail}" if detail else ""))
        else:
            print(f"  FAIL {name}" + (f" {detail}" if detail else ""))
            CHECK_FAILS.append(name)

    tooth("admit_must", admit(L.MUST, MAX_LEAF + 10**9))
    tooth("admit_rs_recent_small", admit(L.RS, 100, True))
    tooth("admit_rs_recent_large", not admit(L.RS, MAX_LEAF + 1, True))
    tooth("admit_rs_old", not admit(L.RS, 100, False))
    # expand-terminal ≠ plan-drop: step gate << MAX_LEAF → recent steps still KEEP
    tooth("expand_terminal_ne_admit_leaf",
          GRAPH_STEP_EXPAND_MAX < MAX_LEAF
          and GRAPH_STEP_EXPAND_MAX < 1024,
          f"step_gate={GRAPH_STEP_EXPAND_MAX} max_leaf={MAX_LEAF}")
    tooth("blob_head_kind_objc",
          blob_head_kind(b"#import <Foundation/Foundation.h>\n") == "objc_hdr"
          and blob_head_kind(b"\x0a\x20" + b"\x00" * 32) == "pb_f1_id32"
          and blob_head_kind(b"\x0a\x20" + b"\x00" * 40) == "pb_f1_id32"
          and blob_head_kind(b"\x00\x01" + b"\x00" * 40) == "binary"
          and blob_head_kind(b"") == "empty")
    free_begin("check free_pulse")
    try:
        free_pulse("t", _force=True)
        tooth("free_pulse_armed", _FREE_T0 > 0 and _FREE_SIG_PREV is not None)
    finally:
        free_end()
    tooth("free_end_restores_sig", _FREE_SIG_PREV is None)
    # Behavioral: undo fence is the organ — not source greps of batch/collide.
    ud = Path(tempfile.mkdtemp(prefix="trim_undo_fence_"))
    try:
        chat_u = ud / "c"; chat_u.mkdir()
        bloated = chat_u / "store.db.bloated-TEST"
        pre = chat_u / "store.db.pretrim-TEST"
        jpre = chat_u / "rollout.jsonl.pretrim-TEST"
        staging = chat_u / "store.db.new-TEST"
        bloated.write_bytes(b"UNDO-B"); pre.write_bytes(b"UNDO-P")
        jpre.write_bytes(b"UNDO-J"); staging.write_bytes(b"STAGING")
        r = retire_siblings(chat_u)
        tooth("undo_fence_keeps_bloated", bloated.exists())
        tooth("undo_fence_keeps_pretrim", pre.exists())
        tooth("undo_fence_retires_staging", not staging.exists())
        tooth("undo_fence_retire_refuses_bloated", retire(bloated) == 0 and bloated.exists())
        trunc = chat_u / "store.db.bloated"
        trunc.write_bytes(b"T")
        tooth("undo_fence_retire_refuses_bloated_trunc",
              is_cut_undo(trunc) and retire(trunc) == 0 and trunc.exists())
        retire(trunc, undo_ok=True)
        pt = chat_u / "x.jsonl.pretrim"
        pt.write_bytes(b"P")
        tooth("undo_fence_retire_refuses_pretrim_trunc",
              is_cut_undo(pt) and retire(pt) == 0 and pt.exists())
        retire(pt, undo_ok=True)
        tooth("undo_fence_retire_refuses_jsonl_pretrim", retire(jpre) == 0 and jpre.exists())
        tooth("undo_fence_retire_undo_ok",
              retire(bloated, undo_ok=True) > 0 and not bloated.exists())
    finally:
        if ud.exists():
            retire(ud, undo_ok=True)

    td = Path(tempfile.mkdtemp(prefix="trim_rel_"))
    try:
        chat = td / "chat"
        chat.mkdir()
        v = judge_reach(chat)
        tooth("judge_reach_tuple", isinstance(v, tuple) and len(v) == 2
              and isinstance(v[0], bool) and isinstance(v[1], str))
        tooth("judge_no_attr_fresh", not hasattr(v, "fresh"))
        tooth("judge_empty_chat", v == (False, "no_live"), str(v))
        (chat / "store.db").write_bytes(b"")
        v2 = judge_reach(chat)
        tooth("judge_no_reachable", v2 == (False, "no_reachable"), str(v2))
        retire(chat / "store.db")

        blobs, root_hex, ids = _synthetic_blobs(n_turns=MIN_TURNS)
        src, dst = td / "s.db", td / "d.db"
        _write_store(src, blobs, root_hex)
        rep = project(src, dst)
        dcon = open_ro(dst)
        kept = {r[0] for r in dcon.execute("SELECT id FROM blobs")}
        dcon.close()
        tooth("project_keep_must", ids["f1"] in kept and ids["arch"] in kept)
        tooth("project_drop_probe_child", ids["arch_c"] not in kept)
        tooth("project_drop_large_rs", ids["step"] not in kept)
        CHECK_INFO["synthetic_keep"] = rep["blobs"]
        CHECK_INFO["mat_gets"] = rep["materialize_sql_gets"]

        blobs1, root1, _ = _synthetic_blobs(n_turns=1)

        src1 = td / "few.db"
        _write_store(src1, blobs1, root1)
        few_ok = False
        try:
            with Snap(src1) as s:
                plan_from(s, 80)
        except SkipChat as e:
            few_ok = e.why.startswith("too_few_turns")
        tooth("skip_too_few_turns", few_ok)

        sub_root = _pb_vid(51)
        view_map, _ = declare_root(_pb_ld(31, _pb_ld(2, sub_root)))
        maps_snap = list(view_map.maps)
        tooth("nested_declare_has_map", maps_snap == [(31, sub_root.hex())], str(maps_snap))
        declare_root(_pb_ld(8, _pb_vid(60)))
        tooth("nested_declare_maps_snap", maps_snap == [(31, sub_root.hex())])
        v1, _ = declare_root(_pb_ld(8, _pb_vid(70)))
        t1 = list(v1.turns)
        v2, _ = declare_root(_pb_ld(8, _pb_vid(72)))
        tooth("declare_independent", t1 == [_pb_vid(70).hex()] and list(v2.turns) == [_pb_vid(72).hex()])

        e1 = turn_edges(_pb_ld(1, _pb_ld(1, _pb_vid(80)) + _pb_ld(2, _pb_vid(81))))
        e1_ids = [r.id for r in e1]
        e2 = turn_edges(_pb_ld(1, _pb_ld(1, _pb_vid(82))))
        tooth("edge_snapshot_stable",
              e1_ids == [r.id for r in e1] and _pb_vid(80).hex() in e1_ids
              and _pb_vid(82).hex() in [r.id for r in e2]
              and _pb_vid(80).hex() not in [r.id for r in e2])

        combo = (
            _pb_ld(1, _pb_ld(1, _pb_vid(90)) + _pb_ld(2, _pb_vid(91)))
            + _pb_ld(8, _pb_vid(92))
            + _pb_ld(31, _pb_ld(2, _pb_vid(93)))
        )
        dual_ids = set()
        for e in turn_edges(combo):
            dual_ids.add(e.id)
        _v, _refs = declare_root(combo)
        for r in _refs:
            dual_ids.add(r.id)
        for tid in _v.turns:
            dual_ids.add(tid)
        for _f, sid in _v.maps:
            dual_ids.add(sid)
        graph_reset()
        _graph_expand_blob(combo)
        tooth("expand_blob_fuse_eq",
              set(GRAPH_QUEUED) == dual_ids
              and _pb_vid(90).hex() in GRAPH_QUEUED
              and _pb_vid(92).hex() in GRAPH_QUEUED
              and _pb_vid(93).hex() in GRAPH_QUEUED,
              f"fuse={sorted(GRAPH_QUEUED)[:6]} dual={sorted(dual_ids)[:6]}")

        live = chat / "store.db"
        shutil.copy2(src, live)
        (chat / "store.db-wal").write_bytes(b"x")
        (chat / "store.db-shm").write_bytes(b"y")
        probes = hold_probes(chat)[:]
        tooth("hold_probes_chat", len(probes) == 3 and probes[0].name == "store.db")
        tooth("hold_probes_file", list(hold_probes(live)) == [live])

        nest_ok = False
        with Snap(src) as a:
            with Snap(dst) as b:
                nest_ok = a._slot == 0 and b._slot == 1 and _SNAP_SLOT == 2
        tooth("snap_pool_nest2", nest_ok and _SNAP_SLOT == 0)

        _lp, _lpm = lock_pids, lock_pids_many
        try:
            lock_pids = lambda _p, fresh=False: [99999]
            lock_pids_many = lambda ts, fresh=False: {t: [99999] for t in ts}
            refused = False
            _err = sys.stderr
            try:
                sys.stderr = open(os.devnull, "w")
                try:
                    require_unlocked(chat, verb="prep")
                except SystemExit:
                    refused = True
            finally:
                sys.stderr.close()
                sys.stderr = _err
            tooth("lock_refuse_prep", refused)
        finally:
            lock_pids, lock_pids_many = _lp, _lpm

        shutil.copy2(src, chat / REACH_NAME)

        write_reach_meta(chat, source_root=root_of(live),
                         snap=FileSnap.take(live, with_root=True), coherent=True)
        fresh, why = judge_reach(chat)
        tooth("judge_fresh_meta", fresh and why == "meta_ok", why)

        with open(live, "ab") as f:
            f.write(b"\x00" * 16)
        fresh2, why2 = judge_reach(chat)
        tooth("judge_live_mutated", (not fresh2) and why2 == "live_mutated_since_prep", why2)

        shutil.copy2(src, live)
        write_reach_meta(chat, source_root=root_of(live),
                         snap=FileSnap.take(live, with_root=True), coherent=True)

        shutil.copy2(live, chat / REACH_NAME)
        write_reach_meta(chat, source_root=root_of(live),
                         snap=FileSnap.take(live, with_root=True), coherent=True)
        bound_before = bound_sibling_bytes(chat) + live.stat().st_size
        try:
            lock_pids = lambda _p, fresh=False: []
            lock_pids_many = lambda ts, fresh=False: {t: [] for t in ts}

            ph = cursor_phase(chat)
            tooth("phase_unlocked_fresh", ph["state"] == "UNLOCKED_FRESH" and ph["allow"]["swap"],
                  ph["state"])
            if ph["allow"]["swap"]:
                out = install_cut_sibling(chat)
                tooth("install_noop_phase", out.get("phase") == "install_noop")
                tooth("install_noop_discards_reach",
                      not (chat / REACH_NAME).exists() and not (chat / REACH_META_NAME).exists())
                bound_after = bound_sibling_bytes(chat) + (chat / "store.db").stat().st_size
                tooth("install_noop_bound_drops", bound_after < bound_before,
                      f"{bound_before}→{bound_after}")
                fr, why = judge_reach(chat)
                ph2 = cursor_phase(chat)
                tooth("install_noop_settled",
                      fr and why == "settled_marker" and (chat / SETTLED_NAME).exists()
                      and ph2.get("kind") == "SETTLED" and ph2["allow"]["prep"] is False
                      and PHASE_ALLOW[(0, "SETTLED")].prep is False,
                      f"{why} kind={ph2.get('kind')}")

                led2 = settle_chat(chat, quiet=True)
                act_names = [next(iter(a)) for a in led2.get("actions", [])]
                tooth("settle_idempotent_settled",
                      "prep" not in act_names and "prep_skip" not in act_names
                      and led2.get("after", {}).get("kind") == "SETTLED",
                      str(act_names))
            else:
                tooth("install_noop_phase", False, "no swap allow")
                tooth("install_noop_discards_reach", False)
                tooth("install_noop_bound_drops", False)
                tooth("install_noop_settled", False)
                tooth("settle_idempotent_settled", False)
        finally:
            lock_pids, lock_pids_many = _lp, _lpm

        dpath = td / "du_tree"
        dpath.mkdir()
        (dpath / "a").write_bytes(b"x" * 4096)
        _DU_CACHE.clear()
        b1 = _du_bytes(dpath)
        tooth("du_miss_then_hit", INSTR["du_miss"] >= 1)
        h0 = INSTR["du_hit"]
        b2 = _du_bytes(dpath)
        tooth("du_cache_hit", INSTR["du_hit"] > h0 and b1 == b2)
        _du_bust(dpath)
        tooth("du_bust", _du_key(dpath) not in _DU_CACHE)
        _du_bytes(dpath)
        tooth("du_after_bust_miss", _du_key(dpath) in _DU_CACHE)

        _parse_lsof_Fn("p1\nn/tmp/a\np2\nn/tmp/b\n")
        tooth("lsof_parse_two", set(_LSOF_BY) >= {"/tmp/a", "/tmp/b"})
        _parse_lsof_Fn("p3\nn/tmp/c\n")
        tooth("lsof_parse_reset", "/tmp/a" not in _LSOF_BY and "/tmp/c" in _LSOF_BY)

        SESSIONS.clear()
        SESSIONS.append(object())

        scan_all(min_mb=10**12, kinds={"cursor"})
        tooth("sessions_refresh", len(SESSIONS) == 0)
        if CURSOR_CHATS.exists():
            h0 = INSTR["scan_win_hit"]
            t0 = INSTR["scan_trust"]
            scan_all(min_mb=10**12, kinds={"cursor"})
            tooth("amort_scan_win", INSTR["scan_win_hit"] > h0,
                  f"hit={INSTR['scan_win_hit']} miss={INSTR['scan_win_miss']}")
            tooth("amort_scan_trust", INSTR["scan_trust"] > t0,
                  f"trust={INSTR['scan_trust']} (hit without restat)")
        else:
            print("SKIP amort_scan_win")
            print("SKIP amort_scan_trust")
        miss_i = INSTR["scan_win_miss"]
        inventory_bytes()
        inventory_bytes()
        tooth("amort_inv_hit", INSTR["inv_hit"] >= 1,
              f"inv_hit={INSTR['inv_hit']} win_missΔ={INSTR['scan_win_miss']-miss_i}")
        harvest_claimed_roots()
        h1 = INSTR["harvest_claim_hit"]
        harvest_claimed_roots()
        tooth("amort_harvest_claim", INSTR["harvest_claim_hit"] > h1)
        transcript_index()
        tx0 = INSTR["tx_win_hit"]
        transcript_index()
        tooth("amort_tx_idx", INSTR["tx_win_hit"] > tx0)
        # fear tooth: nested transcript add must bust TX_WIN (not project-kids-only)
        _tx_td = Path(tempfile.mkdtemp(prefix="trim_txbust_"))
        _tx_root = _tx_td / "projects"
        (_tx_root / "P" / "agent-transcripts" / "A1").mkdir(parents=True)
        (_tx_root / "P" / "agent-transcripts" / "A1" / "A1.jsonl").write_text("{}\n")
        _real_projs, _real_win = CURSOR_PROJS, TX_WIN
        CURSOR_PROJS = _tx_root
        TX_IDX.clear()
        TX_WIN = None
        _i1 = set(transcript_index())
        (_tx_root / "P" / "agent-transcripts" / "A2").mkdir()
        (_tx_root / "P" / "agent-transcripts" / "A2" / "A2.jsonl").write_text("{}\n")
        _i2 = set(transcript_index())
        tooth("tx_fp_nested_bust", _i1 == {"A1"} and _i2 == {"A1", "A2"},
              f"i1={sorted(_i1)} i2={sorted(_i2)}")
        CURSOR_PROJS = _real_projs
        TX_WIN = _real_win
        TX_IDX.clear()
        try:
            retire(_tx_td, undo_ok=True)
        except OSError:
            pass
        if CURSOR_CHATS.exists():
            _scan_cursor_window()
            sample = next((s.path.parent for s in STORE_IDX.values() if s.kind == "cursor"), None)
            if sample is not None:
                b1 = disk_bound_mb(sample)
                ph = cursor_phase(sample)
                tooth("amort_bound_without_phase_lock",
                      abs(b1 - ph["disk_bound_mb"]) < 0.02,
                      f"bound={b1} phase={ph['disk_bound_mb']}")
            else:
                print("SKIP amort_bound_without_phase_lock")
        else:
            print("SKIP amort_bound_without_phase_lock")

        forbidden = {"pip", "npm", "rustup", "browser-brave", "huggingface"}
        tooth("harness_seeds_only",
              "claude-file-history" in PATCHES and not (forbidden & set(PATCHES)),
              f"patches={sorted(PATCHES)}")

        mass = store_mass(chat)
        tooth("store_mass_fields",
              mass.get("file_mb", 0) > 0 and mass.get("graph_mb") is not None
              and mass.get("admit_drop_mb") is not None
              and mass.get("out_of_graph_mb") is not None
              and "dead_mb" not in mass)
        tooth("admit_buckets_present",
              isinstance(mass.get("admit_buckets"), dict)
              and any(k in (mass.get("admit_buckets") or {})
                      for k in ("old_turn", "recent_large", "probe_large", "other")),
              str(mass.get("admit_buckets")))

        EXC_SIDECAR.clear(); LAST_EXC.clear()
        lab = record_exception("tooth", RuntimeError("sidecar-probe"))
        tooth("exc_sidecar_keeps_tb",
              lab.startswith("tooth:RuntimeError:")
              and LAST_EXC.get("typ") == "RuntimeError"
              and "sidecar-probe" in (LAST_EXC.get("tb") or "")
              and len(EXC_SIDECAR) == 1)
        tooth("unfalsifiable_ledger",
              len(UNFALSIFIABLE_LEDGER) >= 5
              and all(len(row) == 3 for row in UNFALSIFIABLE_LEDGER))

        h0 = INSTR["mass_hit"]
        m1 = store_mass(chat)
        tooth("mass_cache_hit", m1.get("mass_cached") is True and INSTR["mass_hit"] > h0,
              f"hit={INSTR['mass_hit']} cached={m1.get('mass_cached')}")
        _mass_bust(chat / "store.db")
        m2 = store_mass(chat)
        tooth("mass_cache_bust", m2.get("mass_cached") is False and m2.get("graph_mb") is not None)

        tooth("harvest_deny_chats",
              is_product_tree(CURSOR_CHATS, harvest_claimed_roots())
              and "chats" in PRODUCT_DIR_NAMES)
        tooth("phase_allow_table",
              PHASE_ALLOW[(0, "REACH")].swap is True
              and PHASE_ALLOW[(0, "SETTLED")].prep is False
              and PHASE_ALLOW[(0, "SETTLED")].swap is False)

        ENRICH_SKIPS.clear()
        bad = b'{"ok":1}\nNOT_JSON\n{"ok":2}\n'
        rows = list(iter_jsonl(bad, kind="test", sid="enrich_off"))
        tooth("enrich_skip_offset",
              len(rows) == 2 and len(ENRICH_SKIPS) == 1
              and ENRICH_SKIPS[0].get("off") == len(b'{"ok":1}\n')
              and ENRICH_SKIPS[0].get("err"),
              str(ENRICH_SKIPS))

        sib_chat = td / "sibchat"
        sib_chat.mkdir()
        sib_file = sib_chat / "store.db.bak-dup"
        sib_file.write_bytes(b"sib")
        SIB_PATHS.clear()
        for p in (sib_file, sib_chat / "." / "store.db.bak-dup"):
            try:
                key = p.resolve()
            except OSError:
                key = p
            SIB_PATHS[key] = None
        tooth("inoc_sib_resolve_unique",
              len(SIB_PATHS) == 1 and next(iter(SIB_PATHS)) == sib_file.resolve(),
              str(list(SIB_PATHS)))
        paths = list_sibling_paths(sib_chat)
        tooth("sib_paths_ordered_unique",
              len(paths) == 1 and paths[0] == sib_file.resolve(),
              str(paths))
        h_sib = INSTR["sib_win_hit"]
        paths2 = list_sibling_paths(sib_chat)
        tooth("amort_sib_win",
              INSTR["sib_win_hit"] > h_sib and paths2 == paths,
              f"hit={INSTR['sib_win_hit']}")

        graph_reset()
        _graph_enqueue("")
        _graph_enqueue(None)  # type: ignore[arg-type]
        tooth("inoc_graph_reject_empty", len(GRAPH_ORDER) == 0 and len(GRAPH_QUEUED) == 0)

        with Snap(src) as s:
            n_g, _ = codec_graph(s)
            tip = s.tip()
        tooth("graph_order_bfs",
              n_g == len(GRAPH_ORDER) == len(GRAPH_QUEUED)
              and GRAPH_HEAD == len(GRAPH_ORDER)
              and GRAPH_ORDER[0] == tip
              and tip in GRAPH_QUEUED,
              f"n={n_g} head={GRAPH_HEAD} order0={GRAPH_ORDER[0][:12] if GRAPH_ORDER else None}")

        tooth("patch_tip_keep_only",
              PATCHES["claude-file-history"].guard == PatchGuard.OPEN
              and not hasattr(PATCHES["claude-file-history"], "broom")
              and callable(patch_tip_keep)
              and PatchGuard.OPT_IN.value > 0)
        # H4 seal: tip organ = last snap; undo near-names already protected
        tooth("undo_near_names_protected",
              is_cut_undo(Path("store.db.pretrim"))
              and is_cut_undo(Path("store.db.bloated"))
              and is_cut_undo(Path("agent.jsonl.pretrim"))
              and is_cut_undo(Path("store.db.pretrim-20990101T000000Z"))
              and not is_cut_undo(Path("store.db"))
              and not is_cut_undo(Path("store.db.reachable")))
        # H4: tip-keep Trashes superseded @v and tip-dropped stems — intentional organ
        fh = td / "fh_tip"
        sess = fh / "sess-h4"
        sess.mkdir(parents=True)
        (sess / "stemA@v1").write_bytes(b"old")
        (sess / "stemA@v2").write_bytes(b"new")
        (sess / "gone@v1").write_bytes(b"drop")
        (sess / "keep_alone").write_bytes(b"k")
        _real_tip = _file_history_tip_named
        def _fake_tip(sid):
            if sid == "sess-h4":
                return {"stemA@v2", "keep_alone"}
            return _real_tip(sid)
        _file_history_tip_named = _fake_tip
        try:
            rep = patch_tip_keep(Patch("test-fh", (fh,), PatchGuard.OPEN))
            tooth("h4_tip_keeps_last_snap",
                  (sess / "stemA@v2").exists() and (sess / "keep_alone").exists(),
                  str(rep))
            tooth("h4_tip_trashes_superseded_v",
                  not (sess / "stemA@v1").exists())
            tooth("h4_tip_trashes_dropped_stem",
                  not (sess / "gone@v1").exists())
        finally:
            _file_history_tip_named = _real_tip
        tooth("kind_registry",
              set(KIND) == set(KINDS)
              and all(hasattr(KIND[k], "scan") for k in KINDS))

        reclaim = default_reclaim_names()
        tooth("inoc_reclaim_harness_only",
              reclaim == ["claude-file-history"]
              and "pip" not in PATCHES and "rustup" not in PATCHES,
              f"reclaim={reclaim} patches={sorted(PATCHES)}")

        tw = evaluate_tripwires()
        for row in tw["tripwires"]:
            tooth(f"tripwire_{row['id']}_clear", not row["fired"], row.get("detail", ""))
        CHECK_INFO["tripwires"] = tw

        GRAPH_ORDER.append("corrupt-dup")
        tooth("tripwire_T4_can_fire", graph_walk_corrupt())
        GRAPH_ORDER.pop()
        tooth("tripwire_T4_clears", not graph_walk_corrupt())
        if GRAPH_QUEUED:
            stolen = next(iter(GRAPH_QUEUED))
            GRAPH_QUEUED.discard(stolen)
            GRAPH_QUEUED.add("corrupt-alien")
            tooth("tripwire_T4_membership_can_fire", graph_walk_corrupt())
            GRAPH_QUEUED.discard("corrupt-alien")
            GRAPH_QUEUED.add(stolen)
            tooth("tripwire_T4_membership_clears", not graph_walk_corrupt())

        stolen_k = KIND.pop("cursor", None)
        tooth("tripwire_T6_can_fire", evaluate_tripwires()["tripwires"][2]["fired"] is True)
        if stolen_k is not None:
            KIND["cursor"] = stolen_k
        tooth("tripwire_T6_clears", evaluate_tripwires()["tripwires"][2]["fired"] is False)

        d2 = td / "du_coh"
        d2.mkdir()
        (d2 / "x").write_bytes(b"z" * 2048)
        st = d2.stat()
        parent_key = str(d2.resolve())
        _DU_CACHE[parent_key] = (st.st_mtime_ns, st.st_ino, 999999)
        stale = _du_bytes(d2)
        auth = _du_bytes(d2, fresh=True)
        tooth("cohere_du_fresh_beats_mtime",
              stale == 999999 and auth < 999999,
              f"stale={stale} auth={auth}")
        (d2 / "y").write_bytes(b"q")
        _DU_CACHE[parent_key] = (0, 0, 888888)
        retire(d2 / "y")
        tooth("cohere_du_lineage_bust", parent_key not in _DU_CACHE)

        probe = td / "lockprobe"
        probe.write_bytes(b"p")
        _LSOF_CACHE.clear()
        lock_pids_many([probe], fresh=False)
        h0 = INSTR["lsof_hit"]
        lock_pids_many([probe], fresh=False)
        tooth("cohere_lsof_fp_hit", INSTR["lsof_hit"] > h0)
        probe.write_bytes(b"p2")
        m0 = INSTR["lsof_miss"]
        lock_pids_many([probe], fresh=False)
        tooth("cohere_lsof_fp_miss_on_mutate", INSTR["lsof_miss"] > m0)
        k0 = INSTR["lsof_fresh"]
        lock_pids_many([probe], fresh=True)
        tooth("cohere_lsof_fresh", INSTR["lsof_fresh"] > k0)
        # timeout must not cache as free
        _real_run = subprocess.run
        def _boom(*a, **k):
            raise subprocess.TimeoutExpired(cmd=a[0] if a else "lsof", timeout=30)
        subprocess.run = _boom
        LSOF_UNKNOWN.clear()
        _LSOF_CACHE.clear()
        cache_n0 = len(_LSOF_CACHE)
        try:
            lock_pids_many([probe], fresh=True)
            tooth("lsof_timeout_marks_unknown", lock_unknown(probe))
            tooth("lsof_timeout_is_locked", is_locked(probe))
            tooth("lsof_timeout_no_cache", len(_LSOF_CACHE) == cache_n0)
            tooth("lsof_timeout_instr", INSTR["lsof_timeout"] >= 1)
        finally:
            subprocess.run = _real_run
        lock_pids_many([probe], fresh=True)
        tooth("lsof_recover_clears_unknown", not lock_unknown(probe))
        duf = td / "du_timeout"
        duf.mkdir()
        (duf / "z").write_bytes(b"x" * 100)
        _real_co = subprocess.check_output
        def _du_boom(*a, **k):
            raise subprocess.TimeoutExpired(cmd="du", timeout=120)
        subprocess.check_output = _du_boom
        dkey = _du_key(duf)
        with _DU_LOCK:
            _DU_CACHE.pop(dkey, None)
        try:
            z = _du_bytes(duf, fresh=True)
            tooth("du_timeout_returns_zero", z == 0)
            with _DU_LOCK:
                tooth("du_timeout_uncached", dkey not in _DU_CACHE)
            tooth("du_timeout_instr", INSTR["du_timeout"] >= 1)
        finally:
            subprocess.check_output = _real_co
        _LOCK_SNAP = {str(probe): [99999]}
        try:
            tooth("cohere_lock_snap_ignored_when_fresh",
                  99999 not in lock_pids(probe, fresh=True))
        finally:
            _LOCK_SNAP = None

        global _CWD_IDX, _CWD_IDX_FP
        _CWD_IDX = {"planted": "/nope"}
        _CWD_IDX_FP = _cwd_roots_fp()
        tooth("cohere_cwd_fp_hit", _cwd_index().get("planted") == "/nope")
        _CWD_IDX_FP = ("drift",)
        tooth("cohere_cwd_fp_miss", "planted" not in _cwd_index())

    finally:
        try:
            retire(td)
        except OSError:
            pass

    CHECK_INFO["fails"] = list(CHECK_FAILS)
    CHECK_INFO["n_ok"] = "see log"
    return CHECK_INFO if not CHECK_FAILS else {**CHECK_INFO, "failed": list(CHECK_FAILS)}

def cmd_check(_chat=None):
    info = reliability_battery()
    tw = info.get("tripwires") or evaluate_tripwires()
    if info.get("failed") or tw.get("any_fired"):
        print("CHECK FAIL", info)
        sys.exit(3)
    print("CHECK OK", {k: info[k] for k in info if k != "failed"})

def cmd_isolate(chat, recent_n):
    live, reach = chat / "store.db", chat / REACH_NAME
    fresh, why = judge_reach(chat)
    if not fresh:
        if lock_pids(live):
            if not reach.exists():
                die(f"REFUSE isolate: no reachable and store held pids={lock_pids(live)}")
            print(f"  stale ({why}) held — isolate existing sibling")
        else:
            print(f"  stale ({why}) — re-prep")
            prep_cut_sibling(chat, recent_n)
            fresh, why = judge_reach(chat)
            if not fresh:
                print(f"  WARN isolate stale ({why})")
    iso = str(uuid.uuid4())
    iso_dir = chat.parent / iso
    iso_dir.mkdir(parents=True)
    store = iso_dir / "store.db"
    shutil.copy2(reach, store)
    con = sqlite3.connect(store)
    meta = meta_of(con)
    meta["agentId"] = iso
    meta["name"] = f"ISO {iso[:8]}"
    con.execute("UPDATE meta SET value=? WHERE key='0'",
                (json.dumps(meta, separators=(",", ":")).encode().hex(),))
    con.commit(); con.close()
    cli = shutil.which("cursor-agent") or str(AG / "cursor-agent")
    cwd = slug_cwd(chat.parent.name) if chat.parent.name else str(HOME)
    if not Path(cwd).is_dir():
        cwd = str(HOME)
    env = os.environ.copy()
    env["CURSOR_AGENT_DISABLE_DEBUG_LOG"] = "1"
    env.setdefault("NODE_OPTIONS", "--max-old-space-size=2048")
    cmd = [cli, "--resume", iso, "--trust", "--print", "--output-format", "json",
           "Reply with exactly one word: pong"]
    t0 = time.time()
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, cwd=cwd, env=env)
    try:
        out, err = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        proc.kill(); out, err = proc.communicate(timeout=10)
    rss_unit = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    peak = (rss_unit / (1024 * 1024)) if sys.platform == "darwin" else (rss_unit / 1024)
    text = ((out or b"") + (err or b"")).decode("utf-8", "replace")
    oom = "out of memory" in text.lower() or "heap limit" in text.lower()
    ok = proc.returncode == 0 and not oom and peak < 1500 and "pong" in text.lower()
    print(json.dumps(dict(ok=ok, iso=iso, peak_rss_mb=round(peak, 2), rc=proc.returncode, oom=oom,
                          mb=round(store.stat().st_size / 1e6, 2), seconds=round(time.time() - t0, 2),
                          reach_fresh=fresh, reach_why=why, cwd=cwd, rss_via="RUSAGE_CHILDREN")))
    try:
        retire(iso_dir)
    except OSError:
        pass
    if not ok: die("isolate CLI resume failed", 3)
    print("ISOLATE OK")

def cmd_batch(ns: argparse.Namespace) -> None:
    if not ns.yes:
        die("batch requires typing yes (or: trim batch yes)")
    cut = PRESETS.get(ns.preset) or PRESETS["heavy"]
    kinds = _kinds_set(ns.kinds)
    lim = int(getattr(ns, "limit", 0) or 0)
    rows = scan_all(ns.min_mb, kinds=kinds, limit=lim)
    print(f"BATCH {ns.preset} · {len(rows)} targets · ≥{ns.min_mb}MB · {cut}")
    results = apply_cuts(rows, cut, swap=False, verify=True)
    ok = sum(1 for r in results if not r.get("error") and not r.get("skipped"))
    # cut leaves undo; batch must not retire
    print(f"\nBATCH done — {ok}/{len(results)} cut  (pretrims KEPT for restore)")

def cmd_restore(ns: argparse.Namespace) -> None:
    path = ns.path or ns.chat
    if not path: die("restore needs a path: trim restore FILE")
    path = Path(path).expanduser().resolve()
    cands = sorted(path.parent.glob(path.name + ".pretrim-*"),
                   key=lambda p: p.stat().st_mtime, reverse=True)
    if not cands:
        if ".pretrim-" in path.name and path.exists():
            live = path.parent / path.name.split(".pretrim-")[0]
            cands = [path]; path = live
        else:
            die(f"no pretrim backup for {path}")
    bak = cands[0]
    if is_locked(path): die(f"LOCKED {path} pids={lock_pids(path)}")
    snap = FileSnap.take(path) if path.exists() else None
    live_bak = path.with_suffix(path.suffix + f".prerestore-{time.strftime('%Y%m%dT%H%M%SZ', time.gmtime())}")
    if path.exists():
        try: os.link(path, live_bak)
        except OSError: shutil.copy2(path, live_bak)
    if snap and snap.drifted():
        die("REFUSE restore: live mutated while preparing restore")
    shutil.copy2(bak, path)
    print(f"RESTORE OK {path}\n  from {bak.name}\n  displaced → {live_bak.name}")

def trim_tracking(keep_days: int = 30, vacuum: bool = True) -> dict:
    db = CURSOR_TRACKING
    if not db.exists(): die("ai-code-tracking.db absent")
    if is_locked(db): die(f"LOCKED {db} pids={lock_pids(db)} — quit Cursor")
    sz = db.stat().st_size
    bak = _backup(db)
    snap = FileSnap.take(db)
    cutoff = int(time.time() * 1000) - keep_days * 86_400_000
    con = sqlite3.connect(str(db), timeout=30)
    before = con.execute("SELECT COUNT(*) FROM ai_code_hashes").fetchone()[0]
    con.execute("DELETE FROM ai_code_hashes WHERE createdAt < ?", (cutoff,))
    try: con.execute("DELETE FROM tracked_file_content WHERE createdAt < ?", (cutoff,))
    except sqlite3.Error: pass
    deleted = before - con.execute("SELECT COUNT(*) FROM ai_code_hashes").fetchone()[0]
    con.commit()
    if vacuum:
        con.execute("VACUUM")
    con.close()
    if snap.drifted():
        print("WARN tracking file identity changed during vacuum (external writer?)")
    return dict(kind="tracking", before_mb=round(sz / 1e6, 2),
                after_mb=round(db.stat().st_size / 1e6, 2),
                hashes_deleted=deleted, keep_days=keep_days, backup=bak.name)

def cmd_clutter(ns: argparse.Namespace) -> None:
    if not ns.yes: die("clutter requires typing yes (or: trim clutter yes)")
    cutoff = time.time() - ns.keep_days * 86400
    removed = freed = 0
    if not CURSOR_PROJS.exists():
        print("no projects dir"); return
    targets: list[Path] = []
    for pth in CURSOR_PROJS.glob("*/agent-tools/*"):
        if pth.is_file(): targets.append(pth)
    for pth in CURSOR_PROJS.glob("*/worker.log"):
        targets.append(pth)
    free_pulse("clutter", n=len(targets), _force=True)
    for i, pth in enumerate(targets):
        free_pulse("clutter", i=i, n=len(targets), removed=removed)
        try: st = pth.stat()
        except OSError: continue
        if st.st_mtime < cutoff or st.st_size >= int(ns.min_mb * 1_000_000):
            try:
                freed += retire(pth); removed += 1
            except OSError as e:
                print(f"  skip {pth}: {e}")
    print(json.dumps(dict(kind="clutter", removed=removed, freed_mb=round(freed / 1e6, 2),
                           keep_days=ns.keep_days, dest="Trash"), indent=2))
    print("CLUTTER OK (→ Trash)")

def _kinds_set(raw) -> set:
    if raw in (None, "", "all", "safe", "cursor,codex,claude"):
        return set(KINDS)
    if isinstance(raw, (set, frozenset, list, tuple)):
        return {k for k in raw if k in KINDS}
    return {k.strip() for k in str(raw).split(",") if k.strip()} & set(KINDS)

def _ns(**kw):
    base = dict(
        min_mb=20.0, recent=DEFAULT_RECENT, kinds="all", preset="heavy",
        keep_days=30, limit=0, yes=False, no_vacuum=False, vacuum=True,
        chat=None, path=None,
    )
    base.update(kw)
    if "vacuum" not in kw:
        base["vacuum"] = not base.get("no_vacuum", False)
    return argparse.Namespace(**base)

def _ask_yes(prompt: str) -> bool:
    if not sys.stdin.isatty():
        return False
    try:
        return input(f"{prompt} [yes/N] ").strip().lower() == "yes"
    except EOFError:
        return False

def _resolve_chat(raw) -> Path:
    if not raw:
        die("need a chat directory (the folder that contains store.db)")
    p = Path(raw).expanduser().resolve()
    if p.is_file() and p.name == "store.db":
        p = p.parent
    if not (p / "store.db").exists():
        die(f"no store.db under {p}")
    return p

def print_help() -> None:
    print("""trim — LLM harness only (Cursor / Codex / Claude)

  Shrinks bloated sessions / jsonl for all three:
    Cursor chats (store.db) · Codex rollout-*.jsonl · Claude project *.jsonl

  Just run:  trim

  Or one word:
    map      harness store sizes
    list     big sessions + last prompt
    free     clutter preview, then asks (never live store.db; Ctrl-C safe)
    cut      shrink a chat/session — asks which + level (default: safe)
    check    self-test
    doctor   health check

  cut levels: safe (160 turns, default) | normal (80) | tight (40)
  Does not touch browsers, pip, rustup, xcode, or other home caches.
  Confirm Trash moves with the word: yes
  Cut leaves undo (bloated/pretrim); free never auto-retires undo.
""")

def inventory_bytes() -> dict[str, float]:
    miss0 = INSTR["scan_win_miss"]
    _scan_cursor_window()
    _scan_codex_window()
    _scan_claude_window()
    out: dict[str, float] = {"cursor": 0.0, "codex": 0.0, "claude": 0.0}
    for s in STORE_IDX.values():
        if s.kind in out:
            out[s.kind] += s.mb / 1000.0
    out["tracking"] = (CURSOR_TRACKING.stat().st_size / 1e9) if CURSOR_TRACKING.exists() else 0.0
    if INSTR["scan_win_miss"] == miss0:
        INSTR["inv_hit"] += 1
    else:
        INSTR["inv_miss"] += 1
    return out

def _du_disk_path() -> Path:
    return CURSOR_HOME / "trim_du_cache.json"

def _du_disk_load() -> None:
    """Load cache file without holding _DU_LOCK across disk I/O (watch rot)."""
    global _DU_DISK_LOADED
    with _DU_LOCK:
        if _DU_DISK_LOADED:
            return
    p = _du_disk_path()
    data = None
    if not p.exists():
        with _DU_LOCK:
            if not _DU_DISK_LOADED:
                _DU_DISK_LOADED = True
                INSTR["du_disk_absent"] += 1
        return
    try:
        data = json.loads(p.read_text())
    except Exception:
        with _DU_LOCK:
            if not _DU_DISK_LOADED:
                _DU_DISK_LOADED = True
                INSTR["du_disk_bad"] += 1
        return
    with _DU_LOCK:
        if _DU_DISK_LOADED:
            return
        n = 0
        for k, v in data.items():
            if isinstance(v, list) and len(v) == 3:
                _DU_CACHE[k] = (int(v[0]), int(v[1]), int(v[2]))
                n += 1
        _DU_DISK_LOADED = True
        INSTR["du_disk_load"] += n

def _du_disk_save() -> None:
    """Snapshot under lock; write file outside lock."""
    global _DU_DISK_DIRTY
    with _DU_LOCK:
        if not _DU_DISK_DIRTY:
            return
        payload = {k: list(v) for k, v in _DU_CACHE.items()}
        _DU_DISK_DIRTY = False
    p = _du_disk_path()
    try:
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.with_suffix(".json.tmp")
        tmp.write_text(json.dumps(payload, separators=(",", ":")))
        tmp.replace(p)
        INSTR["du_disk_save"] += 1
    except Exception:
        with _DU_LOCK:
            _DU_DISK_DIRTY = True
        INSTR["du_disk_save_fail"] += 1

def _du_key(path: Path) -> str:
    try:
        return str(path.resolve())
    except OSError:
        return str(path)

def _du_bust(*paths: Path) -> None:
    global _DU_DISK_DIRTY
    with _DU_LOCK:
        for p in paths:
            key = _du_key(p)
            if key in _DU_CACHE:
                _DU_CACHE.pop(key, None)
                _DU_DISK_DIRTY = True
            if str(p) in _DU_CACHE and str(p) != key:
                _DU_CACHE.pop(str(p), None)
                _DU_DISK_DIRTY = True

def _du_bust_lineage(*paths: Path) -> None:
    global _DU_DISK_DIRTY
    with _DU_LOCK:
        dirty = False
        for p in paths:
            try:
                cur = p.resolve()
            except OSError:
                cur = p
            while True:
                key = str(cur)
                if key in _DU_CACHE:
                    _DU_CACHE.pop(key, None)
                    dirty = True
                if cur == HOME or cur.parent == cur:
                    break
                if HOME not in cur.parents and cur != HOME:
                    break
                cur = cur.parent
        if dirty:
            _DU_DISK_DIRTY = True
            INSTR["du_bust_lineage"] += 1

def _du_bytes(path: Path, *, fresh: bool = False) -> int:
    global _DU_DISK_DIRTY
    _du_disk_load()
    if not path.exists():
        return 0
    try:
        st = path.stat()
    except OSError:
        return 0
    key = _du_key(path)
    if not fresh:
        with _DU_LOCK:
            cached = _DU_CACHE.get(key)
            if cached is not None and cached[0] == st.st_mtime_ns and cached[1] == st.st_ino:
                INSTR["du_hit"] += 1
                return cached[2]
        INSTR["du_miss"] += 1
    else:
        INSTR["du_fresh"] += 1
        with _DU_LOCK:
            _DU_CACHE.pop(key, None)
    if path.is_file() or path.is_symlink():
        with _DU_LOCK:
            _DU_CACHE[key] = (st.st_mtime_ns, st.st_ino, st.st_size)
            _DU_DISK_DIRTY = True
        return st.st_size
    try:
        out = subprocess.check_output(
            ["du", "-sk", str(path)], stderr=subprocess.DEVNULL, text=True, timeout=120)
        b = int(out.split()[0]) * 1024
    except subprocess.TimeoutExpired:
        INSTR["du_timeout"] += 1
        return 0  # uncached — do not mint a lasting 0-byte lie
    except Exception:
        INSTR["du_fail"] += 1
        return 0
    with _DU_LOCK:
        try:
            st = path.stat()
            _DU_CACHE[key] = (st.st_mtime_ns, st.st_ino, b)
        except OSError:
            _DU_CACHE[key] = (0, 0, b)
        _DU_DISK_DIRTY = True
    return b

def _file_history_tip_named(sess_id: str) -> set[str] | None:
    """Last file-history-snapshot only — reverse scan, early exit."""
    if not CLAUDE_PROJS.exists():
        return None
    hits = list(CLAUDE_PROJS.glob(f"*/{sess_id}.jsonl"))
    if not hits:
        return None
    tip = None
    try:
        blob = hits[0].read_bytes()
    except OSError:
        return None
    for o, _off in iter_jsonl_reverse(blob, kind="claude_fh", sid=sess_id):
        if isinstance(o, dict) and o.get("type") == "file-history-snapshot":
            tip = o
            break
    if tip is None:
        return None
    named: set[str] = set()
    backs = (tip.get("snapshot") or {}).get("trackedFileBackups") or {}
    for m in backs.values():
        bn = (m or {}).get("backupFileName")
        if bn:
            named.add(bn)
    return named

def patch_tip_keep(cp: Patch) -> dict:
    """Sole patch free organ: keep LAST file-history-snapshot names (or newest @v stem).

    Tip-shrink is intentional: names absent from the tip (superseded @v or dropped stems)
    go to Trash. keep_days is clutter/tracking's organ — not this one.
    """
    from collections import defaultdict
    removed = 0; freed = 0; kept = 0; tip_sessions = 0; stem_sessions = 0
    for root in cp.roots:
        if not root.exists(): continue
        if lock_pids(root):
            return dict(kind=cp.name, organ="tip_keep", skipped_roots_locked=1, note=cp.note)
        try:
            sessions = [p for p in root.iterdir() if p.is_dir() and not p.name.startswith(".")]
        except OSError:
            continue
        free_pulse("tip_keep", root=root.name, n_sess=len(sessions), _force=True)
        for i, sess in enumerate(sessions):
            free_pulse("tip_keep:read", i=i, n=len(sessions), removed=removed, kept=kept,
                       sess=sess.name[:12], _force=True)
            tip = _file_history_tip_named(sess.name)
            free_pulse("tip_keep", i=i, n=len(sessions), removed=removed, kept=kept)
            if tip is not None and len(tip) == 0:
                tip = None  # empty last snap → stem keep-latest, not freeze
            if tip is not None:
                tip_sessions += 1
                for f in list(sess.iterdir()):
                    if not f.is_file() or f.name.startswith("."): continue
                    try: sz = f.stat().st_size
                    except OSError: continue
                    if f.name in tip:
                        kept += 1; continue
                    try: freed += retire(f); removed += 1
                    except OSError: pass
                continue
            stem_sessions += 1
            groups: dict[str, list] = defaultdict(list)
            for f in sess.iterdir():
                if not f.is_file() or f.name.startswith("."): continue
                try: sz = f.stat().st_size
                except OSError: continue
                if "@v" in f.name:
                    key, _, ver = f.name.rpartition("@v")
                    try: groups[key].append((int(ver), sz, f))
                    except ValueError: groups[f.name].append((0, sz, f))
                else:
                    groups[f.name].append((0, sz, f))
            for vers in groups.values():
                vers.sort()
                for i, (_v, sz, f) in enumerate(vers):
                    if i == len(vers) - 1:
                        kept += 1; continue
                    try: freed += retire(f); removed += 1
                    except OSError: pass
    return dict(kind=cp.name, organ="tip_keep", removed=removed, kept=kept,
                freed_mb=round(freed / 1e6, 2), tip_sessions=tip_sessions,
                stem_fallback_sessions=stem_sessions, note=cp.note)

def free_preview(keep_days: int = 30, min_mb: float = 20.0) -> dict:
    """What free would move to Trash — no mutations. Does not touch live store.db."""
    cutoff = time.time() - keep_days * 86400
    clutter_n = clutter_mb = 0.0
    free_pulse("preview:clutter", _force=True)
    if CURSOR_PROJS.exists():
        targets = list(CURSOR_PROJS.glob("*/agent-tools/*")) + list(CURSOR_PROJS.glob("*/worker.log"))
        for i, pth in enumerate(targets):
            free_pulse("preview:clutter", i=i, n=len(targets))
            if not pth.is_file():
                continue
            try:
                st = pth.stat()
            except OSError:
                continue
            if st.st_mtime < cutoff or st.st_size >= int(min_mb * 1_000_000):
                clutter_n += 1
                clutter_mb += st.st_size / 1e6
    sib_n = sib_mb = 0.0
    locked_skip = 0
    free_pulse("preview:scan-chats", _force=True)
    _scan_cursor_window()
    chats = [s.chat_dir for s in STORE_IDX.values()
             if s.kind == "cursor" and s.chat_dir]
    free_pulse("preview:lsof-batch", n_chats=len(chats), _force=True)
    held = lock_pids_many(chats, fresh=True) if chats else {}
    for i, chat in enumerate(chats):
        free_pulse("preview:siblings", i=i, n=len(chats), sib_n=int(sib_n))
        if held.get(chat):
            locked_skip += 1
            continue
        for p in list_sibling_paths(chat):
            if is_cut_undo(p):
                continue
            try:
                sib_n += 1
                sib_mb += p.stat().st_size / 1e6
            except OSError:
                pass
    hist_mb = 0.0
    p = PATCHES.get("claude-file-history")
    if p:
        free_pulse("preview:du-file-history", _force=True)
        for root in p.roots:
            if root.exists():
                hist_mb = _du_bytes(root) / 1e6
    return dict(
        clutter_files=int(clutter_n), clutter_mb=round(clutter_mb, 1),
        sibling_files=int(sib_n), sibling_mb=round(sib_mb, 1),
        locked_chats_skipped=locked_skip,
        tracking="will age-trim if unlocked" if CURSOR_TRACKING.exists() else "absent",
        claude_file_history_mb=round(hist_mb, 1),
        never=["live store.db", "cut undo (bloated/pretrim/prerestore)", "permanent delete"],
    )

def cmd_reclaim(ns):
    """Free harness clutter only — never live stores or bloated cut-undos."""
    free_begin("FREE — measuring clutter (heartbeat every 5s)…")
    total = 0.0
    t0 = time.time()
    try:
        prev = free_preview(ns.keep_days, ns.min_mb)
        print("FREE preview (harness clutter only — not live chats):")
        print(f"  agent-tools/worker.log  ~{prev['clutter_mb']}MB  ({prev['clutter_files']} files)")
        print(f"  non-undo siblings       ~{prev['sibling_mb']}MB  ({prev['sibling_files']} files)")
        print(f"  tracking                {prev['tracking']}")
        print(f"  claude file-history     ~{prev['claude_file_history_mb']}MB (keep last tip-snap names)")
        print(f"  skipped locked chats    {prev['locked_chats_skipped']}")
        print(f"  never touches           {', '.join(prev['never'])}")
        if not ns.yes:
            # release SIGINT to default during prompt so Ctrl-C aborts cleanly at ask
            free_end()
            if not _ask_yes("Move that clutter to macOS Trash? (Ctrl-C cancels)"):
                die("aborted — or: trim free yes")
            ns.yes = True
            free_begin("FREE running…")
        else:
            print("FREE running…", flush=True)
            free_pulse("run", _force=True)

        free_pulse("clutter", _force=True)
        cmd_clutter(_ns(yes=True, keep_days=ns.keep_days, min_mb=ns.min_mb))

        if CURSOR_TRACKING.exists() and not is_locked(CURSOR_TRACKING):
            free_pulse("tracking", _force=True)
            print("  tracking: trimming…", flush=True)
            rep = trim_tracking(ns.keep_days, vacuum=True)
            freed = max(0.0, rep.get("before_mb", 0) - rep.get("after_mb", 0))
            total += freed
            print(f"  tracking: {rep}")
        elif CURSOR_TRACKING.exists():
            print(f"  tracking: SKIP locked pids={lock_pids(CURSOR_TRACKING)}")

        for name in default_reclaim_names():
            p = PATCHES.get(name)
            if p is None:
                continue
            free_pulse(f"patch:{name}", _force=True)
            print(f"  {name}: tip-keep…", flush=True)
            before = sum(_du_bytes(r, fresh=True) for r in p.roots) / 1e6
            rep = patch_tip_keep(p)
            _du_bust_lineage(*p.roots)
            after = sum(_du_bytes(r, fresh=True) for r in p.roots) / 1e6
            total += max(0.0, before - after)
            print(f"  {name}: {rep}  {before:.1f}→{after:.1f}MB")

        free_pulse("siblings", _force=True)
        _scan_cursor_window()
        chats = [s.chat_dir for s in STORE_IDX.values()
                 if s.kind == "cursor" and s.chat_dir]
        held = lock_pids_many(chats, fresh=True) if chats else {}
        sib_free = 0.0
        for i, chat in enumerate(chats):
            free_pulse("siblings", i=i, n=len(chats), freed_mb=round(sib_free, 1))
            if held.get(chat):
                continue
            r = retire_siblings(chat)
            sib_free += r.get("freed_mb", 0)
            if r.get("removed"):
                print(f"  siblings {chat.name[:8]}: {r}")
        total += sib_free
        _du_disk_save()
        print(f"FREE done — ~{total:.1f} MB → Trash  {time.time()-t0:.1f}s")
    except KeyboardInterrupt:
        print(f"FREE stopped by user after {time.time()-t0:.1f}s — "
              f"~{total:.1f} MB already in Trash kept", flush=True)
    finally:
        free_end()

def cmd_map(ns):
    """Harness inventory only — Cursor/Codex/Claude stores + tracking. No home-cache du."""
    t0 = time.time()
    inv = inventory_bytes()
    print("MAP harness GB", {k: round(v, 3) for k, v in inv.items()},
          "total", round(sum(inv.values()), 3))
    rows = scan_all(1.0, kinds=set(KINDS), limit=25)
    if rows:
        print(f"{'MB':>10}  {'kind':<7}  {'lock':<5}  id / cwd")
        for s in rows:
            print(f"{s.mb:10.1f}  {s.kind:<7}  {'LOCK' if s.locked else 'ok':<5}  "
                  f"{s.sid[:12]}  {clip(s.cwd, 40) or '—'}")
    for root in HARNESS_ROOTS:
        if root.exists():
            print(f"  root {root}")
    print(f"INSTR map {time.time()-t0:.2f}s {dict(INSTR)}")

def harvest_claimed_roots() -> set:
    """Harness product trees only (no home-cache seed list)."""
    global HARVEST_CLAIMED_READY
    if HARVEST_CLAIMED_READY and HARVEST_CLAIMED:
        INSTR["harvest_claim_hit"] += 1
        return HARVEST_CLAIMED
    INSTR["harvest_claim_miss"] += 1
    HARVEST_CLAIMED.clear()
    for prod in HARNESS_ROOTS:
        try:
            HARVEST_CLAIMED.add(prod.resolve())
        except OSError:
            HARVEST_CLAIMED.add(prod)
    for p in PATCHES.values():
        for r in p.roots:
            try:
                HARVEST_CLAIMED.add(r.resolve())
            except OSError:
                HARVEST_CLAIMED.add(r)
    HARVEST_CLAIMED_READY = True
    return HARVEST_CLAIMED

def is_product_tree(kid: Path, claimed: set) -> bool:
    if kid.name in PRODUCT_DIR_NAMES:
        return True
    try:
        rp = kid.resolve()
    except OSError:
        return True
    for c in claimed:
        if rp == c or c in rp.parents:
            return True
    return False

def cmd_harvest(ns):
    die("harvest removed — TRIM only measures LLM harness stores "
        "(~/.cursor/chats, ~/.codex/sessions, ~/.claude/projects)")

def tooth(name, cond, detail=""):
    global PRESSURE_FAILS
    print(("OK " if cond else "FAIL ") + name + ((" " + detail) if detail else ""))
    if not cond:
        PRESSURE_FAILS += 1

def cmd_pressure(_=None):
    global _LOCK_SNAP, PRESSURE_FAILS
    t0 = time.time()
    PRESSURE_FAILS = 0
    if CURSOR_CHATS.exists():
        _scan_cursor_window()
        chats = [s.path.parent for s in STORE_IDX.values() if s.kind == "cursor"]
    else:
        chats = []
    if chats:
        tooth("hold_probes_chat", len(hold_probes(chats[0])) >= 1, f"n={len(hold_probes(chats[0]))}")
    held = dict(lock_pids_many(chats)) if chats else {}
    batch_miss = INSTR["lsof_miss"]
    locked = next((c for c in chats if held.get(c)), None)
    _LOCK_SNAP = {str(c): list(held.get(c, [])) for c in chats} if chats else None
    try:
        if locked:
            try:
                prep_cut_sibling(locked); tooth("prep_locked_refuse", False)
            except (SystemExit, SkipChat):
                tooth("prep_locked_refuse", True, cursor_phase(locked)["state"])
        else:
            print("SKIP prep_locked_refuse")
        forbidden = {"pip", "npm", "rustup", "browser-brave", "huggingface", "xcode-deriveddata"}
        tooth("harness_seeds_only",
              "claude-file-history" in PATCHES
              and not (forbidden & set(PATCHES)),
              f"patches={sorted(PATCHES)}")
        tooth("harness_roots",
              all(hasattr(r, "parts") for r in HARNESS_ROOTS)
              and CURSOR_CHATS in HARNESS_ROOTS
              and CODEX_SESS in HARNESS_ROOTS
              and CLAUDE_PROJS in HARNESS_ROOTS)
        if locked:
            _ = lock_pids(locked)
            tooth("lsof_cache", INSTR["lsof_hit"] >= 1,
                  f"hit={INSTR['lsof_hit']} miss={INSTR['lsof_miss']} chats={len(chats)}")
        tooth("lsof_batch", batch_miss <= 1,
              f"batch_miss={batch_miss} total_miss={INSTR['lsof_miss']} fresh={INSTR['lsof_fresh']} (batch ≤1; gate fresh separate)")
    finally:
        _LOCK_SNAP = None
    print(f"PRESSURE {'OK' if not PRESSURE_FAILS else 'FAIL'} ({PRESSURE_FAILS} failures) {time.time()-t0:.2f}s")
    print(f"INSTR pressure {dict(INSTR)}")
    return PRESSURE_FAILS

def cmd_collide(ns):
    if not ns.yes: die("collide requires typing yes (or: trim advanced collide yes)")
    t0 = time.time()
    cmd_map(ns)
    cmd_reclaim(_ns(**{**vars(ns), "yes": True}))
    settle_all_chats(DEFAULT_RECENT, min_bound_mb=5.0)
    kinds = _kinds_set(ns.kinds)
    scanned = scan_all(ns.min_mb, kinds=kinds, limit=int(getattr(ns, "limit", 0) or 0))
    held = lock_pids_many([s.path for s in scanned if s.kind == "cursor"])
    rows = [s for s in scanned if s.kind != "cursor" or not held.get(s.path)]
    results = apply_cuts(rows, PRESETS["heavy"], swap=False, verify=True)
    # cut leaves undo siblings; retire is a separate organ
    fails = cmd_pressure(ns)
    print(f"COLLIDE {'FAIL' if fails else 'OK'} {time.time()-t0:.0f}s INSTR {dict(INSTR)}")
    if fails: sys.exit(3)

def cmd_doctor(ns=None) -> int:
    ns = ns or _ns()
    fails = cmd_pressure(ns)
    tw = evaluate_tripwires()
    print("TRIPWIRE", "FIRE" if tw["any_fired"] else "CLEAR")
    for row in tw["tripwires"]:
        print(f"  {'FIRE' if row['fired'] else 'ok  '} {row['id']}  {row.get('detail','')}")
    bad = int(fails or 0) + (1 if tw["any_fired"] else 0)
    print(f"DOCTOR {'FAIL' if bad else 'OK'}")
    return bad

def cmd_list(ns=None) -> None:
    ns = ns or _ns()
    print_table(scan_all(ns.min_mb, kinds=_kinds_set(ns.kinds), limit=int(ns.limit or 0)))

def cmd_tripwire(_ns=None) -> int:
    tw = evaluate_tripwires()
    print("TRIPWIRE", "FIRE" if tw["any_fired"] else "CLEAR")
    for row in tw["tripwires"]:
        print(f"  {'FIRE' if row['fired'] else 'ok  '} {row['id']}  {row.get('detail','')}")
    return 3 if tw["any_fired"] else 0

def _ask_line(prompt: str) -> str:
    if not sys.stdin.isatty():
        return ""
    try:
        return input(prompt).strip()
    except EOFError:
        return ""

def pick_cursor_chat() -> Path | None:
    """Show fat cursor chats; user picks a number. Locked ones are labeled — refuse later."""
    rows = [s for s in scan_all(1.0, kinds={"cursor"}, limit=20) if s.chat_dir]
    if not rows:
        print("no cursor chats found")
        return None
    print_table(rows)
    raw = _ask_line("cut which #? (q = cancel) ")
    if not raw or raw.lower() in ("q", "quit", "n", "no"):
        print("cancelled")
        return None
    try:
        i = int(raw)
    except ValueError:
        print("need a number from the list")
        return None
    if i < 1 or i > len(rows):
        print(f"pick 1…{len(rows)}")
        return None
    s = rows[i - 1]
    if s.locked:
        print(f"LOCKED — quit the agent/editor using this chat first (pids on {s.sid[:8]}…)")
        return None
    return s.chat_dir

def pick_cut_level(explicit: str | None = None) -> tuple[str, int]:
    """Return (name, recent_n). Default CUT_DEFAULT=safe (keeps most turns)."""
    if explicit and explicit in CUT_LEVELS:
        return explicit, CUT_LEVELS[explicit]
    print("cut level (how many recent turns to keep in live store):")
    for name, n in CUT_LEVELS.items():
        mark = "  ← default" if name == CUT_DEFAULT else ""
        print(f"  {name:<7}  keep last {n} turns{mark}")
    raw = _ask_line(f"level [{CUT_DEFAULT}]: ").lower() or CUT_DEFAULT
    if raw not in CUT_LEVELS:
        print(f"unknown {raw!r} — using {CUT_DEFAULT}")
        raw = CUT_DEFAULT
    return raw, CUT_LEVELS[raw]

def do_cut(path: str | Path | None = None, *, yes: bool = False,
           level: str | None = None) -> None:
    if path:
        chat = _resolve_chat(path)
    else:
        chat = pick_cursor_chat()
        if not chat:
            return
    lvl_name, recent_n = pick_cut_level(level)
    mb = (chat / "store.db").stat().st_size / 1e6 if (chat / "store.db").exists() else 0
    mass = store_mass(chat)
    keep = mass.get("plan_keep_mb")
    # plan_keep uses DEFAULT_RECENT; re-estimate rough scale by recent ratio when level differs
    if keep is not None and recent_n != DEFAULT_RECENT and DEFAULT_RECENT:
        keep_est = round(keep * (recent_n / DEFAULT_RECENT), 1)
    else:
        keep_est = keep
    print(f"will shrink {chat.name}")
    print(f"  now ~{mb:.0f} MB → keep level={lvl_name} (last {recent_n} turns)")
    if keep_est is not None:
        print(f"  rough keep estimate ~{keep_est} MB (from mass; not exact for this level)")
    print("  safety: refuses if locked; fat kept as store.db.bloated-* (undo — free will not Trash it)")
    print("  restore: trim advanced restore PATH  (from bloated/pretrim while it remains)")
    if not yes and not _ask_yes("Cut this chat?"):
        print("cancelled")
        return
    settle_chat(chat, recent_n)

def cmd_menu() -> None:
    print("TRIM — Cursor / Codex / Claude bloated sessions & jsonl")
    print("  1  map harness stores")
    print("  2  list big chats/sessions")
    print("  3  free harness clutter  (Ctrl-C safe; heartbeats every 5s)")
    print("  4  shrink a chat/session")
    print("  5  self-test")
    print("  6  health check")
    print("  q  quit")
    choice = _ask_line("> ").lower()
    if choice in ("", "q", "quit", "n"):
        return
    table = {
        "1": "map", "map": "map",
        "2": "list", "list": "list",
        "3": "free", "free": "free", "reclaim": "free",
        "4": "cut", "cut": "cut", "settle": "cut",
        "5": "check", "check": "check",
        "6": "doctor", "doctor": "doctor", "help": "help",
    }
    verb = table.get(choice)
    if not verb:
        print("type a number 1–6, or q")
        return
    run_verb(verb, [], yes=False)

# Everyday verbs. Everything else is "advanced <name>".
VERBS = frozenset({
    "map", "list", "free", "cut", "check", "doctor", "help",
    "-h", "--help",
})
ALIASES = {
    "reclaim": "free",
    "settle": "cut",
    "pressure": "doctor",
    "verify": "doctor",
}
ADVANCED = frozenset({
    "cut-all", "settle-all", "tripwire", "coarse", "harvest", "batch",
    "restore", "tracking", "clutter", "collide", "status", "prep",
    "isolate", "swap",
})

def run_verb(verb: str, rest: list, *, yes: bool, _adv: bool = False) -> None:
    verb = ALIASES.get(verb, verb)
    path = None
    clean: list[str] = []
    for tok in rest:
        if tok in ("yes", "--yes"):
            yes = True
            continue
        if tok.startswith("-"):
            die("no flags — run: trim\n  or: trim map|list|free|cut|check|doctor")
        clean.append(tok)
    if clean:
        path = clean[-1]

    ns = _ns(yes=yes, chat=path, path=path)

    if verb in ("help", "-h", "--help"):
        print_help(); return
    if verb == "map":
        cmd_map(ns); return
    if verb == "list":
        cmd_list(ns); return
    if verb == "free":
        cmd_reclaim(ns); return
    if verb == "cut":
        level = None
        chat_path = None
        for tok in clean:
            if tok in CUT_LEVELS:
                level = tok
            else:
                chat_path = tok
        do_cut(chat_path, yes=yes, level=level); return
    if verb == "check":
        cmd_check(None); return
    if verb == "doctor":
        sys.exit(3 if cmd_doctor(ns) else 0)

    if verb == "advanced":
        if not clean:
            print("advanced commands:", ", ".join(sorted(ADVANCED)))
            print("example: trim advanced harvest")
            return
        run_verb(clean[0], clean[1:], yes=yes, _adv=True)
        return

    if verb in ADVANCED and not _adv:
        die(f"{verb} is advanced — run: trim advanced {verb}")

    if verb in ("cut-all", "settle-all"):
        settle_all_chats(DEFAULT_RECENT, min_bound_mb=5.0); return
    if verb == "tripwire":
        sys.exit(cmd_tripwire(ns))
    if verb == "coarse":
        cmd_coarse(ns); return
    if verb == "harvest":
        cmd_harvest(ns); return
    if verb == "batch":
        cmd_batch(ns); return
    if verb == "restore":
        cmd_restore(ns); return
    if verb == "tracking":
        print(trim_tracking(ns.keep_days, vacuum=ns.vacuum)); return
    if verb == "clutter":
        cmd_clutter(ns); return
    if verb == "collide":
        cmd_collide(ns); return
    if verb == "status":
        cmd_status(_resolve_chat(path)); return
    if verb == "prep":
        cmd_prep(_resolve_chat(path), DEFAULT_RECENT); return
    if verb == "isolate":
        cmd_isolate(_resolve_chat(path), DEFAULT_RECENT); return
    if verb == "swap":
        install_cut_sibling(_resolve_chat(path)); return

    die(f"unknown {verb!r}\n  run: trim\n  or: trim map|list|free|cut|check|doctor")

def main():
    av = [a for a in sys.argv[1:] if a not in ("--yes",)]
    yes = "--yes" in sys.argv[1:] or "yes" in sys.argv[1:]
    # strip bare yes from tokens
    av = [a for a in av if a != "yes"]
    if not av:
        if sys.stdin.isatty():
            cmd_menu()
        else:
            print_help()
        return
    if av[0].startswith("-") and av[0] not in ("-h", "--help"):
        die("no flags — run: trim")
    run_verb(av[0], av[1:], yes=yes)

if __name__ == "__main__":
    main()
