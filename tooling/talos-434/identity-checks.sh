#!/usr/bin/env bash

check_hash() {
  local actual
  actual="$(sha256sum "$2")" || return 1
  actual="${actual%% *}"
  if [[ "$actual" != "$1" ]]; then
    echo "overlay identity mismatch: $2 ($actual, expected $1)" >&2
    return 1
  fi
}

check_revision() {
  local actual
  actual="$(git -C "$2" rev-parse HEAD)" || return 1
  if [[ "$actual" != "$1" ]]; then
    echo "$3 revision mismatch: $actual, expected $1" >&2
    return 1
  fi
}

check_pristine_revision() {
  check_revision "$@" || return 1
  if ! git -C "$2" diff --quiet || ! git -C "$2" diff --cached --quiet; then
    echo "$3 source differs from pinned revision" >&2
    return 1
  fi
}

check_toolchain() {
  local actual
  actual="$(tr -d '\r\n' < "$2")" || return 1
  if [[ "$actual" != "$1" ]]; then
    echo "toolchain mismatch: $2 ($actual, expected $1)" >&2
    return 1
  fi
}
