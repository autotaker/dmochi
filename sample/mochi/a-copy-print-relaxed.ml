let rec loop () = loop ()
let assume b = if b then () else loop ();;

let get array idx =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx && idx < n );
    f ();;

let make_array = 
    fun size -> let f _ = 0 in (size, f);;

let update array idx value =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx && idx < n );
    let g = fun () -> if Random.bool() then value else f () in
    (n, g);;

let print_int v = ();;

let rec bcopy m src des i =
  if i >= m then
      des
  else let v = get src i in
       let des = update des i v in
       bcopy m src des (i + 1);;

let rec print_array m array i =
  if i >= m then ()
  else let v = get array i in
       let _ = print_int v in
       print_array m array (i + 1);;

let f m src des =
    let array = bcopy m src des 0 in
    print_array m array 0;;

let main n =
    let array1 = make_array n in
    let array2 = make_array n in
    assume(n > 0);
    f n array1 array2;;
