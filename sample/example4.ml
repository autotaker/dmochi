let rec f p =
    let g = fst p in
    let r = g (snd p) in
    r;;

let succ x = x + 1;;
let x = read_int () in
let r = f (succ, x) in
assert(r > x);;
