#!/usr/bin/env bash

fir_run_producer_pair() {
  local jobs="$1"
  local producer="$2"
  local first="$3"
  local second="$4"
  local first_status=0
  local second_status=0

  if (( jobs == 1 )); then
    "$producer" "$first" || first_status=$?
    "$producer" "$second" || second_status=$?
  else
    "$producer" "$first" &
    local first_pid=$!
    "$producer" "$second" &
    local second_pid=$!
    wait "$first_pid" || first_status=$?
    wait "$second_pid" || second_status=$?
  fi
  if (( first_status != 0 || second_status != 0 )); then
    return 1
  fi
}
