let rec f x = assert(x > 0);;
let x = read_int () in
assume (x > 0);
f x;;
