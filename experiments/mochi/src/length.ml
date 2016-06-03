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
		(n-1,g)
		
let rec length = fun p -> 
  if fst p = 0 then 0 
  else
	(let p1 = tail p in
   assert (fst p1 = fst p - 1);
	 let r = length p1 in
	 r + 1);;

let rec make_list = 
	fun n ->
    if n = 0 then
		(let f = fun j -> let rec loop x = loop x in loop () in
		(0,f))
    else 
     (let p1 = make_list (n-1) in
			let m = fst p1 in
			let f = snd p1 in
			let g = fun j ->
				if j = 0 then n
				else
				(let z = f (j - 1) in z) in
			(m+1,g));;

let main n = 
  let xs = make_list n in
  assert (fst xs = n);
  let m = length xs in
  assert (m = n);;
(*
Types:
  main_1857 : X
  fail_1870 : (x_2:bool[x_2] -> (unit -> X) -> X)
  fail_1871 : (x_2:bool[x_2] -> (unit -> X) -> X)
  fail_1872 : (x_2:bool[x_2] -> (unit -> X) -> X)
  length_1299 : (x_2:int -> (int -> (int -> X) -> X) -> (x_10:int[x_10 = x_2] -> X) -> X)
  make_list_1023 : (x_2:int -> (x_4:int[x_4 = x_2] -> (int -> (int -> X) -> X) -> X) -> X)
*)

