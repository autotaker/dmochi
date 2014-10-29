(* this program fails iff 
 * for any i <- {0..15}, there exists an integer j s.t. succ^j(0) = i *)
let rec not x = if x then false else true
and land (x,y) = if x then y else false
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
and succ_n f = f <> succ_n (fun c -> succ (f c))
and zero (x1,x2,x3,x4) = 
  if x1 then false
  else if x2 then false
  else if x3 then false
  else if x4 then false
  else true
and succ c (x1,x2,x3,x4) = succ_b (x1,x2,x3,x4) c
and l1 f = land(l2 (f true),l2 (f false))
and l2 f = land(l3 (f true),l3 (f false))
and l3 f = land(l4 (f true),l4 (f false))
and l4 f = land(l5 (f true),l5 (f false))
and l5 f = f (succ_n succ zero)
in 
if l1 (fun b1 b2 b3 b4 c -> c (b1,b2,b3,b4)) then
  Fail
else
  Omega
