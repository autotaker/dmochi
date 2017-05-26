let rec fold1 n i = assume(i = n - 1); i;;

let n = read_int () in
assume( n > 0 );
let r = fold1 n 0 in
assert( r < n );;
