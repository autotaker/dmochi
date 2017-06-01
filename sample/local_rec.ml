let search n k =
    let rec sub1 i =
        let rec sub2 j =
            if j >= n 
            then sub1 (i + 1)
            else if i + j = k 
            then (i, j)
            else sub2 (j + 1) in
        if i >= n then (-1, -1)
        else sub2 0 in
    sub1 0;;
let n = read_int () in
let k = read_int () in
let res = search n k in
let i = fst res in
let j = snd res in
if i >= 0 then
    (assert( i + j = k ); ());;

    


