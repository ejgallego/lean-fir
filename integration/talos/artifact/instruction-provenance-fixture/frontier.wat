(module
  (import "lean.extern" "helper"
    (func $helper (param i32 i32) (result i32)))
  (func $entry (param $x i32) (param $y i32) (param $z i32) (result i32)
    ;;@ fir-wasm-origin/1/fixture.entry:1:1
    local.get $x
    ;;@ fir-wasm-origin/1/fixture.entry:2:1
    local.get $y
    ;;@ fir-wasm-origin/1/fixture.entry:3:1
    call $helper
    ;;@ fir-wasm-origin/1/fixture.entry:4:1
    local.get $y
    ;;@ fir-wasm-origin/1/fixture.entry:5:1
    local.get $z
    ;;@ fir-wasm-origin/1/fixture.entry:6:1
    i32.add
    ;;@ fir-wasm-origin/1/fixture.entry:7:1
    i32.mul)
  (func $frontierDead (result i32)
    ;;@ fir-wasm-origin/2/fixture.frontierDead:1:1
    i32.const 30)
  (export "fixture.entry" (func $entry)))
