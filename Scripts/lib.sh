#!/usr/bin/env bash
#
# Shared helper functions for `geometry-of-numbers/Scripts/*.sh`.
#
# Intentionally tiny: keep logic here, keep behavior in the caller scripts.

resolve_lake() {
  # `lake` may not be on PATH in non-interactive shells.
  LAKE="${LAKE:-}"
  if [[ -z "$LAKE" ]]; then
    if [[ -x "$HOME/.elan/bin/lake" ]]; then
      LAKE="$HOME/.elan/bin/lake"
    else
      LAKE="lake"
    fi
  fi
}

# Proof helper CLI resolution (`proofyloops`, with earlier names as fallbacks).
PP_KIND="none"     # none|exe|cargo
PP_EXE=""          # proofyloops|proofpatch|proofloops
PP_BIN=""          # path or command name (when PP_KIND=exe)
PP_MANIFEST=""     # Cargo.toml (when PP_KIND=cargo)
PP_ROOT=""         # sibling checkout root (best effort; may be empty)

resolve_proof_cli() {
  PP_KIND="none"
  PP_EXE=""
  PP_BIN=""
  PP_MANIFEST=""
  PP_ROOT=""

  if [[ -z "${repo_root:-}" ]]; then
    return 1
  fi

  if [[ -d "$repo_root/../proofyloops" ]]; then
    PP_ROOT="$repo_root/../proofyloops"
  elif [[ -d "$repo_root/../proofpatch" ]]; then
    # Back-compat: checkout has not yet been renamed.
    PP_ROOT="$repo_root/../proofpatch"
  elif [[ -d "$repo_root/../proofloops" ]]; then
    # Back-compat: oldest checkout name.
    PP_ROOT="$repo_root/../proofloops"
  fi

  # Prefer the canonical `proofyloops` binary and current package layout.
  if [[ -n "$PP_ROOT" ]]; then
    for p in \
      "$PP_ROOT/target/release/proofyloops" \
      "$PP_ROOT/target/debug/proofyloops" \
      "$PP_ROOT/proofyloops-cli/target/release/proofyloops" \
      "$PP_ROOT/proofyloops-cli/target/debug/proofyloops" \
      "$PP_ROOT/proofyloops-core/target/release/proofyloops" \
      "$PP_ROOT/proofyloops-core/target/debug/proofyloops"
    do
      if [[ -x "$p" ]]; then
        PP_KIND="exe"
        PP_EXE="proofyloops"
        PP_BIN="$p"
        return 0
      fi
    done
  fi
  if command -v proofyloops >/dev/null 2>&1; then
    PP_KIND="exe"
    PP_EXE="proofyloops"
    PP_BIN="proofyloops"
    return 0
  fi
  # Cargo fallback: pick the package manifest that actually defines `proofyloops`.
  #
  # The current binary lives in `proofyloops-cli/`; an early layout used the core crate.
  if [[ -n "$PP_ROOT" ]] && command -v cargo >/dev/null 2>&1; then
    if [[ -f "$PP_ROOT/proofyloops-cli/Cargo.toml" ]]; then
      PP_KIND="cargo"
      PP_EXE="proofyloops"
      PP_MANIFEST="$PP_ROOT/proofyloops-cli/Cargo.toml"
      return 0
    fi
    if [[ -f "$PP_ROOT/proofyloops-core/Cargo.toml" ]]; then
      PP_KIND="cargo"
      PP_EXE="proofyloops"
      PP_MANIFEST="$PP_ROOT/proofyloops-core/Cargo.toml"
      return 0
    fi
  fi

  # Back-compat: `proofpatch` (previous name/layout).
  if [[ -n "$PP_ROOT" ]]; then
    for p in \
      "$PP_ROOT/target/release/proofpatch" \
      "$PP_ROOT/target/debug/proofpatch" \
      "$PP_ROOT/proofpatch-cli/target/release/proofpatch" \
      "$PP_ROOT/proofpatch-cli/target/debug/proofpatch" \
      "$PP_ROOT/proofpatch-core/target/release/proofpatch" \
      "$PP_ROOT/proofpatch-core/target/debug/proofpatch"
    do
      if [[ -x "$p" ]]; then
        PP_KIND="exe"
        PP_EXE="proofpatch"
        PP_BIN="$p"
        return 0
      fi
    done
  fi
  if command -v proofpatch >/dev/null 2>&1; then
    PP_KIND="exe"
    PP_EXE="proofpatch"
    PP_BIN="proofpatch"
    return 0
  fi
  if [[ -n "$PP_ROOT" ]] && command -v cargo >/dev/null 2>&1; then
    if [[ -f "$PP_ROOT/proofpatch-cli/Cargo.toml" ]]; then
      PP_KIND="cargo"
      PP_EXE="proofpatch"
      PP_MANIFEST="$PP_ROOT/proofpatch-cli/Cargo.toml"
      return 0
    fi
    if [[ -f "$PP_ROOT/proofpatch-core/Cargo.toml" ]]; then
      PP_KIND="cargo"
      PP_EXE="proofpatch"
      PP_MANIFEST="$PP_ROOT/proofpatch-core/Cargo.toml"
      return 0
    fi
  fi

  # Back-compat: `proofloops` (oldest name/layout).
  if [[ -n "$PP_ROOT" ]]; then
    for p in \
      "$PP_ROOT/target/release/proofloops" \
      "$PP_ROOT/target/debug/proofloops" \
      "$PP_ROOT/proofloops-core/target/release/proofloops" \
      "$PP_ROOT/proofloops-core/target/debug/proofloops"
    do
      if [[ -x "$p" ]]; then
        PP_KIND="exe"
        PP_EXE="proofloops"
        PP_BIN="$p"
        return 0
      fi
    done
  fi
  if command -v proofloops >/dev/null 2>&1; then
    PP_KIND="exe"
    PP_EXE="proofloops"
    PP_BIN="proofloops"
    return 0
  fi
  if [[ -n "$PP_ROOT" ]] && [[ -f "$PP_ROOT/proofloops-core/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
    PP_KIND="cargo"
    PP_EXE="proofloops"
    PP_MANIFEST="$PP_ROOT/proofloops-core/Cargo.toml"
    return 0
  fi

  return 1
}

pp_run() {
  local subcmd="${1:-}"
  shift || true
  case "$PP_KIND" in
    exe)
      "$PP_BIN" "$subcmd" "$@"
      ;;
    cargo)
      cargo run --manifest-path "$PP_MANIFEST" --bin "$PP_EXE" -- "$subcmd" "$@"
      ;;
    *)
      return 127
      ;;
  esac
}

# Prefer a “fresh” cargo run when available.
#
# Rationale: in a super-workspace, it's common to have a stale prebuilt binary under
# `../proofyloops/target/release/` while the source has moved on. For the LLM review path, using the
# current sources matters because it controls prompt-bounding and redaction behavior.
pp_run_fresh() {
  local subcmd="${1:-}"
  shift || true
  # Prefer running from sources (fresh) when we have a sibling checkout.
  # Use whichever crate manifest defines the selected CLI in this checkout.
  if [[ "$PP_EXE" == "proofyloops" ]] && [[ -n "$PP_ROOT" ]] && command -v cargo >/dev/null 2>&1; then
    if [[ -f "$PP_ROOT/proofyloops-cli/Cargo.toml" ]]; then
      cargo run --manifest-path "$PP_ROOT/proofyloops-cli/Cargo.toml" --bin proofyloops -- "$subcmd" "$@"
      return $?
    fi
    if [[ -f "$PP_ROOT/proofyloops-core/Cargo.toml" ]]; then
      cargo run --manifest-path "$PP_ROOT/proofyloops-core/Cargo.toml" --bin proofyloops -- "$subcmd" "$@"
      return $?
    fi
  fi
  if [[ "$PP_EXE" == "proofpatch" ]] && [[ -n "$PP_ROOT" ]] && command -v cargo >/dev/null 2>&1; then
    if [[ -f "$PP_ROOT/proofpatch-cli/Cargo.toml" ]]; then
      cargo run --manifest-path "$PP_ROOT/proofpatch-cli/Cargo.toml" --bin proofpatch -- "$subcmd" "$@"
      return $?
    fi
    if [[ -f "$PP_ROOT/proofpatch-core/Cargo.toml" ]]; then
      cargo run --manifest-path "$PP_ROOT/proofpatch-core/Cargo.toml" --bin proofpatch -- "$subcmd" "$@"
      return $?
    fi
  fi
  # Back-compat: older repo name/layout.
  if [[ "$PP_EXE" == "proofloops" ]] && [[ -n "$PP_ROOT" ]] && [[ -f "$PP_ROOT/proofloops-core/Cargo.toml" ]] && command -v cargo >/dev/null 2>&1; then
    cargo run --manifest-path "$PP_ROOT/proofloops-core/Cargo.toml" --bin proofloops -- "$subcmd" "$@"
    return $?
  fi
  pp_run "$subcmd" "$@"
}
