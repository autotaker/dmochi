let rec sub2 sub1 n k i j =
    assert( j >= 0 );
    if j >= n then sub1 n k (i + 1)
    else if i + j = k 
    then (i,j)
    else sub2 sub1 n k i (j + 1) 
and sub1 n k i =
    assert( i >= 0 );
    if i >= n then (-1, -1)
    else sub2 sub1 n k i 0;;

let search n k = sub1 n k 0;;
let n = read_int () in
let k = read_int () in
let res = search n k in
let i = fst res in
let j = snd res in
if i >= 0 then
    (assert( i + j = k ); ());;

    


