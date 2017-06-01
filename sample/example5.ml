let x = read_int () in
let f x y = x + y in
let g = f x in
let e = assume(x > 0); g 0 in
assert(x >= 0);
let h x = assert(x > 0);fun y -> x + y in
let i h = assume(false); h 0 0 in
i h;;
