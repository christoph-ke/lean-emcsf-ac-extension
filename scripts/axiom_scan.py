#!/usr/bin/env python3
"""Axiom scan of every project constant.

Elaborates a transient (untracked) Lean file importing every module under `EmcsfAcExtension/`, collects the axioms
of every non-internal constant declared in a project module, and fails on any axiom other than `propext`,
`Classical.choice`, `Quot.sound` — except `sorryAx` in the exports of manifest entries whose state is `DRAFT_SORRY`.

usage: scripts/axiom_scan.py            (transient file under $AXIOM_SCAN_TMP, default .lake/verification)
"""
from __future__ import annotations

import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

ELAB = r'''
open Lean Elab Command in
elab "#project_axiom_scan" : command => do
  let env ← getEnv
  let mut n : Nat := 0
  for (name, _) in env.constants.toList do
    let some m := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[m.toNat]!
    if !(modName.toString.startsWith "EmcsfAcExtension") then continue
    if name.isInternal then continue
    n := n + 1
    let axs ← Lean.collectAxioms name
    for a in axs do
      if a != ``propext && a != ``Classical.choice && a != ``Quot.sound then
        logInfo m!"AXIOM {name} {a}"
  logInfo m!"SCANNED {n}"
#project_axiom_scan
'''


def main() -> int:
    modules = sorted(".".join(p.relative_to(REPO).with_suffix("").parts)
                     for p in (REPO / "EmcsfAcExtension").rglob("*.lean"))
    manifest = json.loads((REPO / "FROZEN_MANIFEST.json").read_text())
    drafts = {a["export"] for a in manifest["anchors"] if a.get("state") == "DRAFT_SORRY"}
    tmp = Path(os.environ.get("AXIOM_SCAN_TMP", REPO / ".lake" / "verification"))
    tmp.mkdir(parents=True, exist_ok=True)
    path = tmp / "AxiomScan.lean"
    path.write_text("".join(f"import {m}\n" for m in modules) + ELAB)
    proc = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", "-j", "4", str(path)],
                          cwd=REPO, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    scanned = re.findall(r"SCANNED (\d+)", out)
    if proc.returncode != 0 or not scanned:
        print("AXIOM SCAN FAILED TO RUN:\n" + "\n".join(out.splitlines()[-20:]), file=sys.stderr)
        return 1
    bad = []
    for name, axiom in re.findall(r"AXIOM (\S+) (\S+)", out):
        if axiom == "sorryAx" and name in drafts:
            continue
        bad.append(f"{name}: {axiom}")
    if bad:
        print("AXIOM SCAN FAILED:", *bad, sep="\n- ", file=sys.stderr)
        return 1
    print(f"AXIOM SCAN OK ({scanned[0]} project constants; sorryAx only in {len(drafts)} DRAFT_SORRY anchors)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
