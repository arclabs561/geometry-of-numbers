#!/usr/bin/env bash
set -euo pipefail

# Install versioned git hooks into .git/hooks/.
#
# We intentionally avoid `git config core.hooksPath` so this repo does not depend on local git config.

repo_root="$(git rev-parse --show-toplevel)"
cd "$repo_root"

if [[ ! -d ".git/hooks" ]]; then
  echo "error: .git/hooks not found (is this a git repo?)" >&2
  exit 1
fi

install_one() {
  local name="$1"
  local src="scripts/hooks/${name}"
  local dst=".git/hooks/${name}"
  if [[ ! -f "$src" ]]; then
    echo "error: missing $src" >&2
    exit 1
  fi
  cp "$src" "$dst"
  chmod +x "$dst"
  echo "installed: $dst"
}

install_one pre-commit
install_one pre-push

echo "ok"

