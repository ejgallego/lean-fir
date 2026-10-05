(module
  ;; Keep the sampled callee active across a bounded batch. The tiny former
  ;; leaf sometimes had no sampled entry-to-leaf parent edge in V8's raw tree.
  (func $leaf (param i32) (result i32)
    (local $batch i32)
    i32.const 1024
    local.set $batch
    block $done
      loop $again
        local.get 0
        i32.eqz
        br_if $done
        local.get $batch
        i32.eqz
        br_if $done
        local.get 0
        i32.const 1
        i32.sub
        local.set 0
        local.get $batch
        i32.const 1
        i32.sub
        local.set $batch
        br $again
      end
    end
    local.get 0)
  (func $entry (param i32) (result i32)
    (local i32)
    local.get 0
    local.set 1
    block $done
      loop $again
        local.get 1
        i32.eqz
        br_if $done
        local.get 1
        call $leaf
        local.set 1
        br $again
      end
    end
    local.get 1)
  (export "fixture.entry" (func $entry)))
