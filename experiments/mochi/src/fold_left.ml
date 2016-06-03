let head =
	fun p -> 
		let f = snd p in
		let z = f 0 in
		z;;
		
let tail =
	fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j -> let v = f (j + 1) in v in
    (n-1,g);;

let nil =
	fun n -> 
		let f = fun j -> 
      let rec loop x = loop x in loop () in
    (0,f);;

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
      if j = 0 then
        x
      else
        let z = f (j - 1) in z in
    (n+1,g);;

let rec fold_left  =
  fun f -> fun acc -> fun xs -> 
    if fst xs = 0 then
      acc
    else
    (let xs1 = tail xs in
     let x   = head xs in
     let acc1 = f acc x in
     let r   = fold_left f acc1 xs1 in
     r);;

let rec make_list = 
	fun n ->
    if n = 0 then
		(let p = nil 0 in
		 p)
    else
		(let p1 = make_list (n-1) in
		 let p2 = cons n p1 in
		 p2);;

let add =
  fun x -> fun y -> x + y;;

let main n m = 
  let xs = make_list n in
  let r = fold_left add m xs in
  assert (r >= m);;
(*
Types:
  main_2204 : X
  fail_2222 : (x_2:bool[x_2] -> (unit -> X) -> X)
  fold_left_1428 : ((x_3:int -> x_4:int[1 <= x_4] -> (x_6:int[1 <= -x_3 + x_6] -> X) -> X) ->
                    x_9:int ->
                    int ->
                    (int -> (x_14:int[1 <= x_14] -> X) -> X) -> (x_18:int[1 <= -x_9 + x_18; x_18 >= x_9] -> X) -> X)
  make_list_1041 : (x_2:int -> (int[x_2 >= 0; 1 <= x_2] -> (int -> (x_8:int[1 <= x_8] -> X) -> X) -> X) -> X)
*)

