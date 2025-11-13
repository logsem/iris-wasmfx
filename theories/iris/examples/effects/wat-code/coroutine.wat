(module ;; coroutine
  (type $func (func))
  (type $cont (cont $func))
  (tag $t)
  (func $yield                         ;; takes no arguments
    (suspend $t))                      ;; and just suspends
  (func $par
    (param $f1 (ref $func))            ;; takes two functions as arguments
    (param $f2 (ref $func))
    (local $current (ref $cont))       ;; local variables:
    (local $next (ref $cont))
    (local $next_is_done i32)
    i32.const 0                        ;; $next_is_done := false
    local.set $next_is_done
    local.get $f1                      ;; $current := cont(f1)
    cont.new $cont
    local.set $current
    local.get $f2                      ;; $next := cont(f2)
    cont.new $cont
    local.set $next
    (loop $l
        (block $b (result (ref $cont))
          local.get $current           ;; resume continuation $current
          resume $cont (on $t $b)
          local.get $next_is_done      ;; if it terminates, and $next_is_done
          br_if 2                  ;; return
          i32.const 1                  ;; $next_is_done := true
          local.set $next_is_done
          local.get $next              ;; $current := $next
          local.set $current
          br $l)                       ;; loop
        local.set $current             ;; else (if effect is triggered) $current := cont
        local.get $next_is_done        ;; if $next_is_done
        br_if $l                       ;; loop
        local.get $current             ;; swap $current $next
        local.get $next
        local.set $current
        local.set $next
        br $l))                        ;; loop
  (export "yield" (func $yield))       ;; make $yield available
  (export "par" (func $par)))          ;; and $par
