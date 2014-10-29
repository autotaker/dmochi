(* this program fails iff 
 * there exists an positive integer j s.t. succ^j(0) = 0 mod 16 *)
let rec not x = if x then false else true
and succ_b (x1,x2,x3,x4) k = 
  if not(x4) then
    k (x1,x2,x3,true)
  else if not(x3) then
    k (x1,x2,true,false)
  else if not(x2) then
    k (x1,true,false,false)
  else if not(x1) then
    k (true,false,false,false)
  else
    k (false,false,false,false)
and is_zero c = c (false,false,false,false)
and zero (x1,x2,x3,x4) = 
  if x1 then false
  else if x2 then false
  else if x3 then false
  else if x4 then false
  else true
and succ c (x1,x2,x3,x4) = succ_b (x1,x2,x3,x4) c
and g c = if is_zero c then Fail else g (succ c)
in g (succ zero)
