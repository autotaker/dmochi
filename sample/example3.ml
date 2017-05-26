let rec f x = (fst x, fst x + snd x);;

let x = read_int () in
let y = read_int () in
assume (x > 0);
assume (y > 0);
let x = fst (x, true) in
let r = f (x, y) in
assert (snd r <= 0);;
