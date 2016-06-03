let head =
	fun p -> 
		let f = snd p in
		let z = f 0 in
		z;;
		
let tail = 
	fun p ->
		let n = fst p in
		let f = snd p in
		let g  = fun j -> let v = f (j + 1) in v in
		(n-1,g)
		
let nil =
	fun n -> 
		let f = fun j -> (0,0) in
		(0,f)

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
			if (j = 0) then x 
      else (let z = f (j - 1) in z) in
		(n+1,g)
			   
let rec make_list =
	fun n ->
    if n = 0 then
		(let p = nil 0 in p)
    else
		(let p1 = make_list (n-1) in
		 let p2 = cons (n,n) p1 in
		 p2);;


let rec for_all =
  fun f -> fun xs -> 
    if fst xs = 0 then true 
    else
    (let x = head xs in
     let xs1 = tail xs in
     let b = f x in
     if b then 
       let z = for_all f xs1 in z
     else false);;

let main n = 
  let xs = make_list n in
  let eq_pair = fun p -> fst p = snd p in
  let z = for_all eq_pair xs in
  assert z;;

(*
Types:
  main_2242 : X
  fail_2258 : (x_2:bool[x_2] -> (unit -> X) -> X)
  for_all_1492 : ((x_3:int -> x_4:int[x_4 = x_3] -> (x_6:bool[x_6] -> X) -> X) ->
                  x_9:int[x_9 = 0] ->
                  (int -> (x_13:int -> x_14:int[x_14 = x_13] -> X) -> X) -> (x_18:bool[x_18] -> X) -> X)
  make_list_1031 : (int -> (x_4:int[x_4 = 0] -> (int -> (x_8:int -> x_9:int[x_9 = x_8] -> X) -> X) -> X) -> X)
*)
