(module
  (func $leaf (param i32) (result i32)
    local.get 0
    i32.const 1
    i32.add)
  (func $entry (param i32) (result i32)
    local.get 0
    call $leaf)
  (func $dead (result i32)
    i32.const 17)
  (export "fixture.entry" (func $entry)))
