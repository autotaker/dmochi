let nil n = assume false; 0;;
let cons x f = let g j = x in g;;
let rec fold_left acc xs =
    if read_int () = 0
    then acc
    else 
        let x = xs 0 in
        fold_left (acc + x) xs;;

let rec make_list n = 
    if read_int () = 0
    then nil
    else cons n (make_list (n-1));;

let n = read_int () in
let m = read_int () in
let xs = make_list n in
let r = fold_left m xs in
assert( r >= m );;


    

