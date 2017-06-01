let rec fold1 g n i =
    assert( i < n );
    if i = n - 1
    then i
    else g i (fold1 g n (i + 1));;

let n = read_int () in
let g x y = if x >= y then x else y in
assume( n > 0 );
assert( fold1 g n 0 < n );;

