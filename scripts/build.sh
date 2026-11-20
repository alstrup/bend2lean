#!/bin/bash
# Translate the Taylor-shift proofs to Lean, append the bridge theorem, and check it.
#   BEND_DIR=<bend checkout> LEAN=<lean binary> scripts/build.sh
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
LEAN=${LEAN:-lean}
cd "$ROOT/examples/taylor"
bun "$ROOT/bend2lean.ts" SIMPROOF2.bend "$ROOT/lean/Taylor.gen.lean"
cat "$ROOT/lean/Taylor.gen.lean" "$ROOT/lean/FastBridge.lean" > "$ROOT/lean/Taylor.lean"
"$LEAN" "$ROOT/lean/Taylor.lean" | grep -E "error|fast_taylor_shift|ashift_ok"
