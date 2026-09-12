#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel)"
tmp_root="$(mktemp -d "${TMPDIR:-/tmp}/gon-proofyloops-test.XXXXXX")"
trap 'rm -rf "$tmp_root"' EXIT

fake_root="$tmp_root/work space"
fake_gon="$fake_root/gon"
fake_pp="$fake_root/proofyloops"
fake_bin="$fake_pp/target/debug/proofyloops"
fake_path="$tmp_root/bin"
capture="$tmp_root/capture"
counter="$tmp_root/rubberduck-count"
llm_counter="$tmp_root/llm-count"

mkdir -p "$fake_gon" "$fake_pp/target/debug" "$fake_path"
ln -s "$repo_root/Scripts" "$fake_gon/Scripts"

printf '#!/usr/bin/env bash\nprintf "%%s\\n" "$FAKE_GIT_ROOT"\n' > "$fake_path/git"
chmod +x "$fake_path/git"

printf '%s\n' '#!/usr/bin/env bash' > "$fake_bin"
printf '%s\n' 'set -euo pipefail' >> "$fake_bin"
printf '%s\n' 'printf "%s\\n" "$@" >> "$FAKE_CAPTURE"' >> "$fake_bin"
printf '%s\n' 'if [[ "$1" == "rubberduck-prompt" ]]; then' >> "$fake_bin"
printf '%s\n' '  count=0' >> "$fake_bin"
printf '%s\n' '  [[ -f "$FAKE_COUNTER" ]] && count="$(<"$FAKE_COUNTER")"' >> "$fake_bin"
printf '%s\n' '  count=$((count + 1))' >> "$fake_bin"
printf '%s\n' '  printf "%s" "$count" > "$FAKE_COUNTER"' >> "$fake_bin"
printf '%s\n' '  [[ "$count" -eq 1 ]] && exit 9' >> "$fake_bin"
printf '%s\n' 'fi' >> "$fake_bin"
printf '%s\n' 'if [[ "$1" == "llm-chat" ]]; then' >> "$fake_bin"
printf '%s\n' '  count=0' >> "$fake_bin"
printf '%s\n' '  [[ -f "$FAKE_LLM_COUNTER" ]] && count="$(<"$FAKE_LLM_COUNTER")"' >> "$fake_bin"
printf '%s\n' '  count=$((count + 1))' >> "$fake_bin"
printf '%s\n' '  printf "%s" "$count" > "$FAKE_LLM_COUNTER"' >> "$fake_bin"
printf '%s\n' '  [[ "$count" -eq 1 ]] && exit 10' >> "$fake_bin"
printf '%s\n' 'fi' >> "$fake_bin"
chmod +x "$fake_bin"

export FAKE_GIT_ROOT="$fake_gon"
export FAKE_CAPTURE="$capture"
export FAKE_COUNTER="$counter"
export FAKE_LLM_COUNTER="$llm_counter"
export PATH="$fake_path:$PATH"

input="$fake_root/input with spaces and apostrophe's.json"
bundle="$fake_root/bundle with spaces and apostrophe's"

assert_smt_argv() {
  local -a actual expected
  actual=()
  local arg
  while IFS= read -r arg || [[ -n "$arg" ]]; do
    actual+=("$arg")
  done < "$capture"
  expected=(smt-repro --input-json "$input" --bundle-dir "$bundle")
  if [[ ${#actual[@]} -ne ${#expected[@]} ]]; then
    printf 'expected %s SMT argv entries, got %s\n' "${#expected[@]}" "${#actual[@]}" >&2
    return 1
  fi
  local i
  for ((i = 0; i < ${#expected[@]}; i += 1)); do
    if [[ "${actual[i]}" != "${expected[i]}" ]]; then
      printf 'SMT argv mismatch at index %s\n' "$i" >&2
      return 1
    fi
  done
}

: > "$capture"
"$repo_root/Scripts/smt_capsule.sh" "$input" "$bundle"
assert_smt_argv

if command -v just >/dev/null 2>&1; then
  : > "$capture"
  just smt-capsule "$input" "$bundle"
  assert_smt_argv
else
  printf 'just unavailable; skipped Justfile SMT quoting check\n' >&2
fi

report_output="$tmp_root/report-output"
GON_ARTIFACT_DIR="$tmp_root/artifacts" GON_LLM_DUCK=0 "$repo_root/Scripts/check.sh" report > "$report_output" 2>&1

grep -Fqx '3' "$counter"
grep -F '[check:report] warning: rubberduck prompt generation failed (non-blocking)' "$report_output" >/dev/null

llm_output="$tmp_root/llm-output"
GON_ARTIFACT_DIR="$tmp_root/llm-artifacts" GON_LLM_DUCK=1 "$repo_root/Scripts/check.sh" report > "$llm_output" 2>&1

grep -Fqx '3' "$llm_counter"
grep -F '[check:report] warning: llm-chat failed (non-blocking)' "$llm_output" >/dev/null

printf 'proofyloops integration checks passed\n'
