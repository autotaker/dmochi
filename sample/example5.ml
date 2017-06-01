let x = read_int () in
let f x y = x + y in
let g = f x in
let e = assume( x > 0); g 0 in
assert(x < 0);;
