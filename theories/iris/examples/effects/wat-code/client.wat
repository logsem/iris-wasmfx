;; run with the specfx fork of the reference interpreter with
;; ./wasm coroutine.wat -e '(module instance)' -e '(register "coroutine")' client.wat -e '(module instance)' -e '(invoke "main")'
;; it should display
;; [0 42] : [i32 i32]
(module ;; client
  (type $func (func))
  (import "coroutine" "yield" (func $yield)) ;; needs yield and par
  (import "coroutine" "par" (func $par (param (ref $func)) (param (ref $func))))
  (global $x (mut i32) (i32.const 0))        ;; shared `data' $x
  (global $y (mut i32) (i32.const 0))        ;; shared `flag' $y
  (global $a (mut i32) (i32.const 0))        ;; reader's copy of the value of $y
  (global $b (mut i32) (i32.const 0))        ;; reader's copy of the value of $x
  (elem declare funcref (ref.func $f1))      ;; make $f1 available
  (elem declare funcref (ref.func $f2))      ;; and $f2
  (func $f1
    i32.const 42                             ;; write 42 to $x
    global.set $x
    call $yield                              ;; yield
    i32.const 1                              ;; set the flag
    global.set $y)
  (func $f2
    global.get $y                            ;; read from $y
    global.set $a                            ;; save in $a
    call $yield                              ;; yield
    global.get $x                            ;; read from $x
    global.set $b)                           ;; save in $b
  (func $main (result i32 i32)
    ref.func $f1                             ;; run $f1 and $f2 concurrently
    ref.func $f2
    call $par
    global.get $a                            ;; look up what the reader saw
    global.get $b)
  (export "main" (func $main)))              ;; make $main available outside
