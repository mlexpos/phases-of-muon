#!/usr/bin/env python3
"""Full verification of the Muon package (quiet checkpoints only: runs `lake build`).

1. The frozen snapshot is intact (appendix-nodes/common/snapshot.py --check).
2. Every module under Muon/ is reachable from the root `Muon.lean`.
3. `lake build`.
4. `Audit.lean`: no axiom beyond propext / Classical.choice / Quot.sound / sorryAx in any
   Muon declaration; writes .lake/audit.json.
5. coverage.json is consistent: one row per snapshot label; every listed declaration exists;
   rows marked proved / proved-modulo-external have no sorryAx; frozen rows exist.
Output is also written to verification.log.
"""
import json
import os
import re
import subprocess
import sys
from pathlib import Path

PKG = Path(__file__).resolve().parents[1]
WS = PKG.parents[1]
CAMP = PKG.parent / "phases-of-muon" / "appendix-nodes"
log_lines = []


def say(msg):
    print(msg)
    log_lines.append(msg)


def run(cmd, cwd=PKG):
    env = dict(os.environ, ELAN_HOME=str(WS / ".elan"),
               PATH=f"{WS / '.elan' / 'bin'}:{os.environ.get('PATH', '')}")
    r = subprocess.run(cmd, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log_lines.append("$ " + " ".join(map(str, cmd)) + "\n" + r.stdout)
    if r.returncode:
        print(r.stdout)
        finish(f"FAILED: {' '.join(map(str, cmd))}")
    return r.stdout


def finish(msg):
    say(msg)
    (PKG / "verification.log").write_text("\n".join(log_lines) + "\n")
    sys.exit(0 if msg.startswith("OK") else 1)


# 1. snapshot
say(run([sys.executable, "common/snapshot.py", "--check"], cwd=CAMP).strip())

# 2. reachability
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = PKG / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        finish(f"FAILED: missing local import {module}")
    for imp in re.findall(r"^import\s+(Muon(?:\.[\w]+)*)\s*$", path.read_text(), re.M):
        visit(imp)
visit("Muon")
modules = {str(p.relative_to(PKG).with_suffix("")).replace("/", ".") for p in (PKG / "Muon").rglob("*.lean")}
outside = modules - seen
if outside:
    finish(f"FAILED: modules outside the root import graph: {sorted(outside)}")
say(f"{len(modules)} modules, all reachable from Muon.lean")

# 3-4. build and axiom audit
run(["lake", "build"])
say("lake build passed")
out = run(["lake", "env", "lean", "Audit.lean"])
say(next((l for l in out.splitlines() if "Audited" in l), out.strip()))
audit = {d["name"]: d for d in json.loads((PKG / ".lake" / "audit.json").read_text())}

# 5. coverage
cov = json.loads((PKG / "coverage.json").read_text())
inv = {s["label"] for s in json.loads((CAMP / "inventory" / "inventory.json").read_text())["statements"]}
problems = []
if set(cov["entries"]) != inv:
    problems.append(f"coverage rows vs snapshot labels: missing {sorted(inv - set(cov['entries']))[:5]}, "
                    f"extra {sorted(set(cov['entries']) - inv)[:5]}")
counts = {}
for label, row in cov["entries"].items():
    st = row.get("status")
    counts[st] = counts.get(st, 0) + 1
    for d in row.get("declarations", []):
        if d not in audit:
            problems.append(f"{label}: declaration {d} not found")
        elif st in ("proved", "proved-modulo-external") and audit[d]["sorry"]:
            problems.append(f"{label}: marked {st} but {d} depends on sorryAx")
    if st in ("frozen", "proved", "proved-modulo-external") and not row.get("declarations"):
        problems.append(f"{label}: status {st} without declarations")
    if st == "proved-modulo-external" and not row.get("certificates"):
        problems.append(f"{label}: proved-modulo-external without certificates")
for p in problems:
    say("  " + p)
say("coverage: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())))
finish("FAILED: coverage inconsistent" if problems else "OK: package verified")
