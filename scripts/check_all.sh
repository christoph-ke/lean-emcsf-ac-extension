#!/usr/bin/env bash
# Release checks. The manifest explicitly identifies any remaining draft anchor.
set -euo pipefail
cd -- "$(dirname -- "$0")/.."
if [[ $# -gt 1 || ( $# == 1 && "$1" != --no-build ) ]]; then
  echo "usage: scripts/check_all.sh [--no-build]" >&2
  exit 2
fi
python3 scripts/check_frozen_anchors.py --root . --manifest FROZEN_MANIFEST.json
if [[ "${1:-}" != --no-build ]]; then
  nice -n 10 lake build
fi
python3 scripts/frozen_abi.py frozen --check FROZEN_MANIFEST.json
python3 scripts/axiom_scan.py
echo "CHECK_ALL OK"
