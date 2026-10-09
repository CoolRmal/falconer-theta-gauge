#!/usr/bin/env bash
set -euo pipefail

# Adapted from PalomarRegistry/PalomarTemplate at
# 2891de4c48955af824969a263d31b25e7a9a1406, scripts/verify-comparator.sh.
# Default verification uses Linux's sandbox and all three kernel implementations.
# The explicit --preliminary mode is only for local development on hosts where
# the Linux sandbox is unavailable. It uses Lean's deliberately named
# --inadvisably-no-sandbox flag and is not a Palomar mechanical report.
# Preliminary mode uses dependencies already installed in this checkout and
# does not download a cache; prepare the project before invoking it.
preliminary=false
case "${1:-}" in
  "") ;;
  --preliminary)
    preliminary=true
    shift
    ;;
  --help|-h)
    echo "Usage: $0 [--preliminary]"
    echo "Default: sandboxed Linux Comparator with Lean, NanoDa, and con-ron."
    echo "--preliminary: local sandbox-off check; never accepted as CI verification."
    exit 0
    ;;
  *)
    echo "error: unknown option: $1" >&2
    exit 2
    ;;
esac
if [ "$#" -ne 0 ]; then
  echo "error: unexpected additional arguments" >&2
  exit 2
fi
if "$preliminary" && { [ "${GITHUB_ACTIONS:-}" = true ] || [ "${CI:-}" = true ]; }; then
  echo "error: --preliminary is forbidden in CI; use sandboxed verification" >&2
  exit 1
fi

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"
required_commands=(lake lean python3)
if ! "$preliminary"; then
  required_commands+=(bwrap)
fi
for required_command in "${required_commands[@]}"; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required for this Comparator mode" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

# Palomar supplies these trusted paths itself. They must not be committed in
# comparator.json, where external_kernels is not a permitted submitter field.
# Limit con-ron to the two workers used by Palomar's qualified memory policy.
config=$(mktemp "${TMPDIR:-/tmp}/theta-gauge-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    raise SystemExit(f"error: {source} must contain one JSON object")
if "external_kernels" in config:
    raise SystemExit(f"error: {source}: external_kernels is not a submitter field")
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron", "--jobs=2"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
PY

if ! "$preliminary"; then
  lake exe cache get
fi
if "$preliminary"; then
  echo "PRELIMINARY LOCAL CHECK: sandbox disabled; this is not Palomar verification." >&2
  lake comparator --inadvisably-no-sandbox --config "$config"
else
  lake comparator --config "$config"
fi
