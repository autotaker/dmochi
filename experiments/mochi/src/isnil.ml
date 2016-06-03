let nil =
	fun n -> 
		let f = fun j -> 0 in
		(0,f)

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
			(if (j = 0) then x
       else let z = f (j - 1) in z)in
		(n+1,g)
			   

let rec make_list =
	fun n ->
    if n = 0 then
		(let p = nil 0 in
		 p)
    else
		(let p1 = make_list (n-1) in
		 let p2 = cons n p1 in
		 p2)

let is_nil =
  fun p -> fst p = 0;;

let main n = 
  let xs = make_list n in
  if n > 0 then
    let b = is_nil xs in
    assert (not b);;
(*
Types:
  main_1683 : X
  fail_1693 : (x_2:bool[x_2] -> (unit -> X) -> X)
  make_list_1020 : (x_2:int -> (x_4:int[x_4 >= 0; 1 <= x_4; x_2 <= 0] -> (int -> (int -> X) -> X) -> X) -> X)
*)
