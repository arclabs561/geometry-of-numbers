#!/usr/bin/env bash
set -euo pipefail

# Create an SMT repro capsule through the same proofyloops resolver used by the
# repository's other helper integrations. This supports a sibling checkout and
# keeps paths with spaces intact.

if [[ $# -ne 2 ]]; then
  printf 'usage: %s <pp_dump_json> <bundle_dir>\n' "${0##*/}" >&2
  exit 2
fi

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

source "$repo_root/Scripts/lib.sh"
if ! resolve_proof_cli; then
  printf 'proofyloops not available (need ../proofyloops or proofyloops on PATH)\n' >&2
  exit 127
fi

pp_run_fresh smt-repro --input-json "$1" --bundle-dir "$2"
