let rec sum x =
    if x > 0
    then let y = sum (x - 1) in x + y
    else 0;;

let x = read_int () in
let r = sum x in
assert( r >= x );;
