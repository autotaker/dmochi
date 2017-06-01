let head p = let f = snd p in f 0;;
let tail p = 
    let n = fst p in
    let f = snd p in
    let g i = f (i + 1) in
    (n - 1, g);;

let nil x = let f i = assume(false); (fun y -> 0) in (0, f)

let cons x p = 
    let n = fst p in
    let f = snd p in
    let g i = if i = 0 then x else f (i - 1) in
    (n + 1, g);;

let rec fold_right f xs acc =
    if fst xs = 0 then
        acc
    else
        let x = head xs in
        let xs1 = tail xs in
        let acc1 = fold_right f xs1 acc in
        f x acc1;;

let rec make_list n =
    if n = 0 then nil ()
    else
        let f m = m + n in
        let xs = make_list (n - 1) in
        cons f xs;;

let n = read_int() in
let m = read_int() in
let xs = make_list n in
let compose f g = fun x -> f (g x) in
let f = fold_right compose xs (fun x -> x) in
let r = f m in
assert( r >= m );;
