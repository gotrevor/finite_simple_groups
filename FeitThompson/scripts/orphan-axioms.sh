#!/usr/bin/env bash
# Detect orphan axioms in FeitThompson/: declared but never referenced
# from any other .lean file (no callers, no theorems depending on them).
#
# Origin: Inc 23 (2026-05-26). The autonomous sweep found 3 orphan axioms
# (norm_C_eq_top, wlog_comm_eq_top, abelian_charsimple_special) — leftover
# tree-decomposition scaffolding from when the actual proofs took a
# different route through bundled "assembly" axioms. The orphans had been
# carrying their own soundness risk (any unjustified axiom widens the
# trusted base) for ~10 PRs before anyone noticed.
#
# Usage:
#   FeitThompson/scripts/orphan-axioms.sh             # list orphans
#   FeitThompson/scripts/orphan-axioms.sh --strict    # exit 1 if any
#
# Definition: an axiom is "orphan" if its name appears in exactly one .lean
# file/line (the declaration site itself). Comments and docstrings inside
# .lean files DO count as references — they're not exempt — but they're a
# weak signal. The script treats reference-count=0 as orphan; if you want
# to grandfather a comment-only reference, ignore the report for that name.
#
# False-positive caveats:
#   - Axioms used only via `open` namespacing without an explicit name
#     mention would be missed. Current FT-port convention is to call by
#     fully-qualified name, so this is unlikely in practice.
#   - Axioms re-exported through `export` or wrapper theorems would still
#     be detected as orphan if the wrapper is the only user. Manual review
#     before removal is recommended for any first-time detection.

set -euo pipefail

cd "$(dirname "$0")/../.."  # repo root

STRICT=0
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

orphans=()
all_axioms=$(grep -rnE "^axiom [a-zA-Z_]" FeitThompson/ --include="*.lean" | sort)

while IFS= read -r line; do
  # Each line: "path:lineno:axiom NAME ..."
  name=$(echo "$line" | sed -E 's/^[^:]+:[0-9]+:axiom ([a-zA-Z_][a-zA-Z0-9_]*).*$/\1/')
  if [[ -z "$name" ]]; then continue; fi

  # Count non-declaration references in .lean files.
  refs=$(grep -rE "(^|[^a-zA-Z_])${name}([^a-zA-Z_]|$)" FeitThompson/ --include="*.lean" 2>/dev/null \
         | grep -v "axiom $name" \
         | grep -v "^$" \
         | wc -l \
         | tr -d ' ')

  if [[ "$refs" -eq 0 ]]; then
    site=$(echo "$line" | cut -d: -f1-2)
    orphans+=("$name  ($site)")
  fi
done <<< "$all_axioms"

if [[ ${#orphans[@]} -eq 0 ]]; then
  echo "No orphan axioms detected."
  exit 0
fi

echo "Orphan axioms (declared but never .lean-referenced):"
for o in "${orphans[@]}"; do
  echo "  $o"
done

if [[ "$STRICT" -eq 1 ]]; then
  exit 1
fi
