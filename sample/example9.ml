let rec f x j = 
    assume(j <> 0);
    assert(x >= 0);;
let n = read_int () in
let b = if n >= 0 then 1 else 0 in
let r = f n b in
r;;
