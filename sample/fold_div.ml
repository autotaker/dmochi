let head p = let f = snd p in f 0;;
let tail p = 
    let n = fst p in
    let f = snd p in
    let g i = f (i + 1) in
    (n - 1, g);;

let nil x = let f i = assume(false); 0 in (0, f)

let cons x p = 
    let n = fst p in
    let f = snd p in
    let g i = if i = 0 then x else f (i - 1) in
    (n + 1, g);;

let rec fold_left f acc xs =
    if fst xs = 0 then
        acc
    else
        let x = head xs in
        let xs1 = tail xs in
        let acc1 = f acc x in
        fold_left f acc1 xs1;;

let rand_pos x =
    let r = read_int () in
    assume( r > 0 );
    r;;
(*
    if r > 0 then
        r
    else rand_pos ();;
*)

let rec make_list n =
    if n = 0 then nil ()
    else
        let x = rand_pos () in
        let xs = make_list (n - 1) in
        cons x xs;;

let n = read_int() in
let m = read_int() in
let xs = make_list n in
let div x y = assert(y <> 0); read_int() in
let r = fold_left div m xs in
()
