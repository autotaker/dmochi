let rec mc91 x =
    if x > 100 
    then x - 10
    else mc91 (mc91 (x + 11));;

let n = read_int () in
assume(n <= 101);
assert(mc91 n = 91);;
