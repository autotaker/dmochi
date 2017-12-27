let empty _ =  ((0, 0), 0);;
let rec rotate xs ys acc =
  assert(ys > 0);
  assert(ys = xs + 1);
  if xs = 0 then acc + 1 else 1 + rotate (xs - 1) (ys - 1) (acc + 1);;
let exec xs ys acc =
  if acc > 0 then
    ((xs, ys), acc - 1)
  else
    let f' = rotate xs ys acc in ((f', 0), f');;
let snoc q _ = 
    let xs = fst (fst q) in
    let ys = snd (fst q) in
    let acc = snd q in
    exec xs (ys+1) acc;;
let tail q = 
    let xs = fst (fst q) in
    let ys = snd (fst q) in
    let acc = snd q in
    if xs = 0 then empty () else exec (xs - 1) ys acc;;
let rec loop q =
  if read_int() >= 0 then
    loop (snoc q 0)
  else
    loop (tail q);;
let main n = loop (empty n);;
