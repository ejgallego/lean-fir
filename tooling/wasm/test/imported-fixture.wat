(module
  (import "host" "sink" (func $sink (param i32)))
  (import "host" "identity" (func $identity (param i32) (result i32)))
  (func $leaf (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)
  (func $entry (param i32) (result i32)
    local.get 0
    call $sink
    local.get 0
    call $identity
    call $leaf)
  (func $dead (result i32)
    i32.const 17)
  (export "fixture.entry" (func $entry)))
