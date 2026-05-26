#!/usr/bin/env bash
# Detect dead declarations in FeitThompson/:
#   (a) orphan axioms — declared but never .lean-referenced
#   (b) placeholder theorems returning `True := by trivial` with no refs
#
# Origin:
#   - Inc 23 (2026-05-26): the orphan-axiom audit found 3 orphans
#     (norm_C_eq_top, wlog_comm_eq_top, abelian_charsimple_special) —
#     leftover tree-decomposition scaffolding from when the actual proofs
#     took a different route through bundled "assembly" axioms. Each had
#     been silently widening the trusted base for ~10 PRs.
#   - Inc 24 (2026-05-26): extended to flag dead-True placeholder
#     theorems after the same pattern surfaced in P1_4 (semidirect_solvable,
#     piPart_Fitting_trivial, fitting_in_G).
#
# Orphan axioms are a *soundness* concern (any unjustified axiom widens
# the trusted base). Dead-True placeholders are a *clutter* concern
# (sound but useless). Both indicate the same root cause: tree
# decompositions written as code but never wired up to actual proofs.
#
# Usage:
#   FeitThompson/scripts/orphan-axioms.sh             # report only
#   FeitThompson/scripts/orphan-axioms.sh --strict    # exit 1 if any found
#
# Definition of "orphan/dead": the name appears in exactly one .lean
# file/line (the declaration site itself). Comments and docstrings inside
# .lean files DO count as references — they're not exempt — but they're a
# weak signal. The script treats reference-count=0 as orphan; if you want
# to grandfather a comment-only reference, ignore the report for that name.
#
# False-positive caveats:
#   - Declarations used only via `open` namespacing without an explicit
#     name mention would be missed. Current FT-port convention is to call
#     by fully-qualified name, so this is unlikely in practice.
#   - Declarations re-exported through `export` or wrapper theorems would
#     still be detected as orphan if the wrapper is the only user. Manual
#     review before removal is recommended for any first-time detection.

set -euo pipefail

cd "$(dirname "$0")/../.."  # repo root

STRICT=0
if [[ "${1:-}" == "--strict" ]]; then
  STRICT=1
fi

# Helper: count non-declaration .lean references for a name.
# Args: $1 = kind ("axiom" or "theorem"), $2 = name
count_refs() {
  local kind="$1"
  local name="$2"
  grep -rE "(^|[^a-zA-Z_])${name}([^a-zA-Z_]|$)" FeitThompson/ --include="*.lean" 2>/dev/null \
    | grep -v "$kind $name" \
    | grep -v "^$" \
    | wc -l \
    | tr -d ' '
}

# --- (a) Orphan axioms -------------------------------------------------------

orphan_axioms=()
all_axioms=$(grep -rnE "^axiom [a-zA-Z_]" FeitThompson/ --include="*.lean" | sort)

while IFS= read -r line; do
  [[ -z "$line" ]] && continue
  name=$(echo "$line" | sed -E 's/^[^:]+:[0-9]+:axiom ([a-zA-Z_][a-zA-Z0-9_]*).*$/\1/')
  [[ -z "$name" ]] && continue

  refs=$(count_refs "axiom" "$name")
  if [[ "$refs" -eq 0 ]]; then
    site=$(echo "$line" | cut -d: -f1-2)
    orphan_axioms+=("$name  ($site)")
  fi
done <<< "$all_axioms"

# --- (b) Dead-True placeholder theorems --------------------------------------

dead_placeholders=()

# Match both `theorem foo : True := by trivial` and the multiline form
# `theorem foo ... : True := by\n  trivial` by finding `theorem NAME` lines
# whose subsequent context within ~5 lines shows `: True ` and a `trivial`
# body. Implemented as: grep for theorem-name lines, then check the file
# region for `: True ` + `trivial`.
while IFS= read -r tline; do
  [[ -z "$tline" ]] && continue
  file=$(echo "$tline" | cut -d: -f1)
  lineno=$(echo "$tline" | cut -d: -f2)
  name=$(echo "$tline" | sed -E 's/^[^:]+:[0-9]+:theorem ([a-zA-Z_][a-zA-Z0-9_]*).*$/\1/')
  [[ -z "$name" ]] && continue

  # Read the next ~8 lines from the file; check for `: True ` and `trivial`.
  region=$(sed -n "${lineno},$((lineno + 8))p" "$file")
  if echo "$region" | grep -qE ": True " \
     && echo "$region" | grep -qE "by *trivial|by *exact +trivial|:= +trivial"; then
    refs=$(count_refs "theorem" "$name")
    if [[ "$refs" -eq 0 ]]; then
      dead_placeholders+=("$name  ($file:$lineno)")
    fi
  fi
done < <(grep -rnE "^theorem [a-zA-Z_]" FeitThompson/ --include="*.lean")

# --- Report ------------------------------------------------------------------

found=0

if [[ ${#orphan_axioms[@]} -gt 0 ]]; then
  echo "Orphan axioms (declared but never .lean-referenced):"
  for o in "${orphan_axioms[@]}"; do
    echo "  $o"
  done
  found=1
fi

if [[ ${#dead_placeholders[@]} -gt 0 ]]; then
  [[ "$found" -eq 1 ]] && echo
  echo "Dead-True placeholder theorems (return \`True := by trivial\`, no refs):"
  for d in "${dead_placeholders[@]}"; do
    echo "  $d"
  done
  found=1
fi

if [[ "$found" -eq 0 ]]; then
  echo "No orphan axioms or dead placeholders detected."
  exit 0
fi

if [[ "$STRICT" -eq 1 ]]; then
  exit 1
fi
