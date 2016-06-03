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
		let f = fun j -> 1 in
		(0,f);;

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
		    if j = 0 then
		      x
		    else 
		      let z = f (j - 1) in z
		    in
		(n+1,g);;

let rec fold_left =
  fun f -> fun acc -> fun xs ->
    if fst xs = 0 then 
      acc
    else
    (let xs1 = tail xs in
     let x   = head xs in
     let acc1 = f acc x in
     let r   = fold_left f acc1 xs1 in
     r);;

let rec rand_pos =
    fun y -> 
      let x = Random.int 0 in
      if x > 0 then x else rand_pos y;;

let rec make_list =
	fun n ->
	  if n = 0 then
		(let p = nil 0 in p)
      else
		(let p1 = make_list (n-1) in
         let x  = rand_pos 0 in
		 let p2 = cons x p1 in
		 p2);;


let div = 
  fun x -> fun y ->
    assert (y <> 0);
    Random.int 0;;

let main n m = 
	let xs = make_list n in
	let r = fold_left div m xs in
	r;;
(*
  main_2247 : X
  fail_2270 : (x_2:bool[x_2] -> (unit -> X) -> X)
  fold_left_1436 : ((int -> x_4:int[1 <= x_4] -> (int -> X) -> X) ->
                    int -> x_10:int[x_10 = 0] -> (int -> (x_14:int[1 <= x_14] -> X) -> X) -> (int -> X) -> X)
  make_list_1042 : (int -> (x_4:int[x_4 = 0] -> (int -> (x_8:int[1 <= x_8] -> X) -> X) -> X) -> X)
  rand_pos_1434 : (int -> (x_4:int[1 <= x_4] -> X) -> X)
Verification result

Safe!

Refinement Types:
  fold_left: ((int -> ({x_9:int | x_9 >= 1} -> int)) ->
                  (int -> ((int * (int -> {x_7:int | x_7 >= 1})) -> int)))
  make_list: (int -> (int * (int -> {x_4:int | x_4 >= 1})))
  rand_pos: (int -> {x_2:int | x_2 >= 1})

cycles: 1
total: 0.261 sec
  abst: 0.010 sec
  mc: 0.020 sec
  refine: 0.097 sec
    exparam: 0.000 sec
  
    fold_left_1436 : 
      ((int -> x_4:int[1 <= x_4] -> int) -> int -> 
        x_10:int[x_10 = 0] -> (int -> int[x_14.1 <= x_14]) -> int)
*)

