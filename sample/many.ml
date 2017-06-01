let rec make n =
    if n = 0 then
        fun i -> assume false;0
    else
        let v = read_int () in
        let f = make (n - 1) in
        fun i -> if read_int () = 0 then v else f i;;

let rec filter f n g =
    if n = 0 then
        fun i -> assume false;0
    else 
        let v = g () in
        let g1 = filter f (n - 1) g in
        if f v then
            fun i -> if read_int () = 0 then v else g1 i
        else
            g1;;

let rec map f n g =
    if n = 0 then fun i -> assume false;0
    else let v = f (g ()) in
         let g1 = map f (n -1) g in
         fun i -> if read_int () = 0 then v else g1 i;;

let rec fold f acc n g =
    if n = 0 then acc
    else let v = g () in
    fold f (f acc v) (n - 1) g;;

let xs = make (read_int ()) in
let xs = filter (fun v -> v > 0) (read_int ()) xs in
let r = fold (fun x y -> x + y) 0 (read_int ()) xs in
assert(r >= 0);
let xs = make (read_int ()) in
let xs = filter (fun v -> v > 0) (read_int ()) xs in
let r = fold (fun x y -> x + y) 0 (read_int ()) xs in
assert(r >= 0);
let xs = make (read_int ()) in
let xs = filter (fun v -> v > 0) (read_int ()) xs in
let r = fold (fun x y -> x + y) 0 (read_int ()) xs in
assert(r >= 0);
let xs = make (read_int ()) in
let xs = filter (fun v -> v > 0) (read_int ()) xs in
let r = fold (fun x y -> x + y) 0 (read_int ()) xs in
assert(r >= 0);
let xs = make (read_int ()) in
let xs = filter (fun v -> v > 0) (read_int ()) xs in
let r = fold (fun x y -> x + y) 0 (read_int ()) xs in
assert(r >= 0);;


