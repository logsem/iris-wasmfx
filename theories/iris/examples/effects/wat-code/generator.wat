;; run with the specfx fork of the reference interpreter with
;; ./wasm generator.wat -e '(module instance)' -e '(invoke "sum_until" (i32.const 10))'
;; it should display
;; 55 : [i32]
(module
 (type $func (func))
 (type $cont (cont $func))
 (tag $gen (param i32))

 (func $naturals
  (local $n i32)
  (loop $l
   local.get $n
   suspend $gen
   local.get $n
   i32.const 1
   i32.add
   local.set $n
   br $l
  )
 )

 (elem declare func $naturals)

 (func $sum_until (param $upto i32) (result i32)
  (local $v i32)
  (local $sum i32)
  (local $k (ref $cont))
  ref.func $naturals
  cont.new $cont
  local.set $k
  (loop $l
   (block $on_gen (result i32 (ref $cont))
    local.get $k
    resume $cont (on $gen $on_gen)
    unreachable
   )
   local.set $k
   local.set $v

   local.get $sum
   local.get $v
   i32.add
   local.set $sum

   local.get $v
   local.get $upto
   i32.lt_u
   br_if $l
  )
  local.get $sum
 )

 (export "sum_until" (func $sum_until))

)
