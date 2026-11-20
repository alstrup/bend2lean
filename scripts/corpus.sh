#!/bin/bash
# Translate each of Bend's proof tests to Lean and check it; one line per file.
#   BEND_DIR=<bend checkout> LEAN=<lean binary> scripts/corpus.sh > results/corpus.tsv
ROOT=$(cd "$(dirname "$0")/.." && pwd)
LEAN=${LEAN:-lean}
OUT=$(mktemp -d)
cd "${BEND_DIR:?set BEND_DIR to a bend checkout}"
for f in tests/proof/*.bend; do
  n=$(basename "$f" .bend)
  tr=$(timeout 60 bun "$ROOT/bend2lean.ts" "$f" "$OUT/$n.lean" 2>&1 | grep -E "^translated|^error" | head -1)
  if [ ! -f "$OUT/$n.lean" ] || ! grep -q "^translated" <<<"$tr"; then echo "$n	TRANSLATE-FAIL	${tr:0:80}"; continue; fi
  skip=$(grep -o "skipped [0-9]*" <<<"$tr" | grep -o "[0-9]*")
  timeout 120 "$LEAN" "$OUT/$n.lean" > "$OUT/$n.log" 2>&1; rc=$?
  ok=$(grep -c "does not depend on any axioms" "$OUT/$n.log"); bad=$(grep -c "depends on axioms" "$OUT/$n.log")
  echo "$n	lean=$rc	clean=$ok	sorry=$bad	skipped=$skip"
done
