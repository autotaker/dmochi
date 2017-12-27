let empty _ k =  k 0 0 0;;
let rec rotate xs ys acc =
  (* ys = xs + 1, xs >= 0, acc >= 0 *)
  assert(xs >= 0);
  assert(ys = xs + 1);
  if xs = 0 then acc + 1 else 1 + rotate (xs - 1) (ys - 1) (acc + 1);;
  (* ret >= 0 *)
let exec xs ys acc k =
  (* xs = ys + acc - 1, xs >= 0, acc >= 0 *)
  if acc > 0 then
    k xs ys (acc - 1)
  else
    let f' = rotate xs ys acc in k f' 0 f';;
let snoc xs ys acc _ k = 
    exec xs (ys+1) acc k ;;
let tail xs ys acc k = 
    if xs = 0 then empty () k else exec (xs - 1) ys acc k;;
(* xs = ys + acc, xs >= 0, acc >= 0 *)
let rec loop xs ys acc =
  if read_int() >= 0 then
    snoc xs ys acc 0 loop
  else
    tail xs ys acc loop;;
let main n = empty n loop;;
