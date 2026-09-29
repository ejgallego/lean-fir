(module
  (import "host" "sink" (func $sink (param i32) (result i32)))
  (import "runtime" "adjust" (func $adjust (param i32) (result i32)))
  (func $entry (export "fixture.entry") (param $n i32) (result i32)
    (call $sink (call $adjust (local.get $n))))
  (func $dead (export "fixture.dead") (result i32) (i32.const 999)))
