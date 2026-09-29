(module
  (import "host" "scale" (func $scale (param i32) (result i32)))
  (func $adjust (export "adjust") (param $n i32) (result i32)
    (if (result i32) (i32.eqz (local.get $n))
      (then (call $scale (i32.const 1)))
      (else (i32.add (call $scale (local.get $n))
        (call $adjust (i32.sub (local.get $n) (i32.const 1))))))))
