(module
  (func $helper (param $left i32) (param $right i32) (result i32)
    ;;@ fir-wasm-origin/0/runtime.helper:1:1
    local.get $left
    ;;@ fir-wasm-origin/0/runtime.helper:2:1
    local.get $right
    ;;@ fir-wasm-origin/0/runtime.helper:3:1
    i32.add)
  (func $runtimeDead (result i32)
    ;;@ fir-wasm-origin/1/runtime.dead:1:1
    i32.const 50)
  (export "helper" (func $helper))
  (export "runtime.dead" (func $runtimeDead)))
