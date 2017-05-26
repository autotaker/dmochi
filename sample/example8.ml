let f x = x + 1;;
let g k = let r = k 0 in r;;
let n = read_int () in
let y = f 0 in
let z = g f in
assert(y = z);;

