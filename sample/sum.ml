let rec sum x = 
    if x > 0 
    then x + sum (x - 1)
    else 0;;

let x = read_int () in
let r = sum x in
assert(r >= x);;

