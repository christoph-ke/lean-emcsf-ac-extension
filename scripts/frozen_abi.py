#!/usr/bin/env python3
"""Elaborated-ABI dump and hash of the frozen exports.

For every export the dump records, from the elaborated environment: universe parameters, the type, the value
(definitions only; theorem proofs are excluded so that sealing does not change the ABI), and for structures the
constructor type and field names. Expressions are printed with `Expr.dbgToString` (no pretty-printer options
involved) after normalizing two meaningless elaboration artifacts: auxiliary proof constants `…._proof_N` become a
marker applied to their (normalized) proposition, and macro scopes are erased from binder names. `abi_sha256` in `FROZEN_MANIFEST.json` is the SHA-256 of one export's dump block (UTF-8).

usage:
  scripts/frozen_abi.py frozen              # elaborate against the built frozen modules
  scripts/frozen_abi.py probe FILE.lean     # elaborate a single-file candidate (module header stripped)
  options: --dump DIR  write each block to DIR/<export>.txt;  --json  print {export: sha256};
           --check FROZEN_MANIFEST.json  verify every abi_sha256
The transient Lean file is written under $FROZEN_ABI_TMP (default .lake/verification) and not tracked.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
EXPORTS = [
    "EmcsfAcExtension.Fields", "EmcsfAcExtension.Fields.mu", "EmcsfAcExtension.Fields.a",
    "EmcsfAcExtension.Fields.b", "EmcsfAcExtension.Fields.Omega2", "EmcsfAcExtension.Fields.rUV",
    "EmcsfAcExtension.Fields.mU", "EmcsfAcExtension.Fields.mV", "EmcsfAcExtension.Fields.QU",
    "EmcsfAcExtension.Fields.QV", "EmcsfAcExtension.Fields.AV", "EmcsfAcExtension.Fields.waveSource",
    "EmcsfAcExtension.Fields.thetaU", "EmcsfAcExtension.Fields.xiV", "EmcsfAcExtension.Fields.phiV",
    "EmcsfAcExtension.Fields.phiU", "EmcsfAcExtension.Fields.EqOn", "EmcsfAcExtension.triangle",
    "EmcsfAcExtension.origDomain", "EmcsfAcExtension.outSeg", "EmcsfAcExtension.inSeg",
    "EmcsfAcExtension.IntegralForm", "EmcsfAcExtension.covVarIn", "EmcsfAcExtension.IsSolution",
    "EmcsfAcExtension.signedExpIntegrand", "EmcsfAcExtension.positiveExpIntegrand", "EmcsfAcExtension.datumVar",
    "EmcsfAcExtension.jOut", "EmcsfAcExtension.kIn", "EmcsfAcExtension.charged_main",
    "EmcsfAcExtension.restart_charged_local_BV",
    "EmcsfAcExtension.charged_main_real_uncharged",
]
FROZEN_MODULES = ["EmcsfAcExtension.Frozen.ChargedMain", "EmcsfAcExtension.Frozen.RestartChargedLocalBV",
                  "EmcsfAcExtension.Frozen.ChargedMainRealUncharged"]

ELAB = r'''
open Lean in
/-- Normalize elaboration artifacts that carry no meaning: auxiliary proof constants (`…._proof_N`, named after
the declaration that first created them) are replaced by a marker applied to their normalized proposition, and
macro scopes (hygienic names that embed the module name) are erased from binder names. -/
partial def abiNorm (env : Environment) (e : Expr) : Expr :=
  e.replace fun sub =>
    match sub with
    | .const n _ =>
        if n.components.any (fun c => c.toString.startsWith "_proof_") then
          match env.find? n with
          | some ci => some (mkApp (mkConst `ABI.proofOf) (abiNorm env ci.type))
          | none => none
        else none
    | .forallE n t b bi => some (.forallE n.eraseMacroScopes (abiNorm env t) (abiNorm env b) bi)
    | .lam n t b bi => some (.lam n.eraseMacroScopes (abiNorm env t) (abiNorm env b) bi)
    | .letE n t v b nd => some (.letE n.eraseMacroScopes (abiNorm env t) (abiNorm env v) (abiNorm env b) nd)
    | _ => none

open Lean Elab Command in
elab "#abi_dump " n:ident : command => do
  let env ← getEnv
  let name := n.getId
  let some ci := env.find? name | throwError m!"unknown constant {name}"
  let norm := fun (x : Expr) => (abiNorm env x).dbgToString
  let mut s := s!"NAME {name}\nLEVELS {ci.levelParams}\nTYPE {norm ci.type}\n"
  match ci with
  | .defnInfo d => s := s ++ s!"VALUE {norm d.value}\n"
  | .thmInfo _ => s := s ++ "THEOREM (proof excluded)\n"
  | .inductInfo i =>
      s := s ++ s!"INDUCTIVE params={i.numParams} indices={i.numIndices} ctors={i.ctors}\n"
      for c in i.ctors do
        let some cc := env.find? c | throwError m!"unknown constructor {c}"
        s := s ++ s!"CTOR {c} : {norm cc.type}\n"
      match getStructureInfo? env name with
      | some si => s := s ++ s!"FIELDS {si.fieldNames}\n"
      | none => pure ()
  | _ => s := s ++ "OTHER\n"
  logInfo m!"ABI_BEGIN\n{s}ABI_END"
'''


def lean_file(mode: str, probe: Path | None) -> str:
    if mode == "frozen":
        head = "".join(f"import {m}\n" for m in FROZEN_MODULES)
    else:
        text = probe.read_text()
        text = re.sub(r"(?m)^module\s*$", "", text, count=1)
        text = re.sub(r"(?m)^public import ", "import ", text)
        text = re.sub(r"(?m)^@\[expose\] public section\s*$", "", text)
        head = text + "\n"
    return head + ELAB + "".join(f"#abi_dump {e}\n" for e in EXPORTS)


def run(mode: str, probe: Path | None) -> dict[str, str]:
    tmp = Path(os.environ.get("FROZEN_ABI_TMP", REPO / ".lake" / "verification"))
    tmp.mkdir(parents=True, exist_ok=True)
    path = tmp / f"AbiDump_{mode}.lean"
    path.write_text(lean_file(mode, probe))
    proc = subprocess.run(["nice", "-n", "10", "lake", "env", "lean", "-j", "4", str(path)],
                          cwd=REPO, capture_output=True, text=True)
    out = proc.stdout + proc.stderr
    blocks = re.findall(r"ABI_BEGIN\n(.*?)ABI_END", out, re.S)
    errors = [line for line in out.splitlines() if ": error" in line]
    if errors or len(blocks) != len(EXPORTS):
        sys.exit(f"ABI dump failed ({len(blocks)} blocks):\n" + "\n".join(errors[:20] or out.splitlines()[-20:]))
    result = {}
    for block in blocks:
        name = block.split("\n", 1)[0].removeprefix("NAME ")
        result[name] = block
    if list(result) != EXPORTS:
        sys.exit("ABI dump: export order/name mismatch")
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=["frozen", "probe"])
    parser.add_argument("file", nargs="?", type=Path)
    parser.add_argument("--dump", type=Path)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--check", type=Path, metavar="MANIFEST",
                        help="compare against abi_sha256 in MANIFEST; exit 1 on any mismatch")
    args = parser.parse_args()
    if args.mode == "probe" and not args.file:
        parser.error("probe mode needs FILE")
    result = run(args.mode, args.file)
    hashes = {name: hashlib.sha256(block.encode()).hexdigest() for name, block in result.items()}
    if args.dump:
        args.dump.mkdir(parents=True, exist_ok=True)
        for name, block in result.items():
            (args.dump / f"{name}.txt").write_text(block)
    if args.check:
        manifest = json.loads(args.check.read_text())
        expected = {a["export"]: a["abi_sha256"] for a in manifest["anchors"]}
        bad = sorted(set(expected) ^ set(hashes)) + [n for n in expected if n in hashes and hashes[n] != expected[n]]
        if bad:
            print("FROZEN ABI CHECK FAILED:", *bad, sep="\n- ", file=sys.stderr)
            return 1
        print(f"FROZEN ABI CHECK OK ({len(hashes)} exports)")
        return 0
    if args.json:
        print(json.dumps(hashes, indent=2))
    else:
        for name, digest in hashes.items():
            print(digest, name)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
