let head =
	fun p -> 
    assert (fst p > 0);
		let f = snd p in
		let z = f 0 in
		z;;
		
let tail =
	fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j -> let v = f (j + 1) in v in
		(n-1,g)
		
let nil =
	fun n -> 
		let f = fun j -> 0 in
		(0,f)

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
      if j = 0 then 
        x 
      else
			(let z = f (j - 1) in z) in
		(n+1,g)
			   
let rec length = fun p ->
  if fst p = 0 then 
    0
  else
	(let p1 = tail p in
	 let r = length p1 in
	 r + 1);;

let rec make_list =
	fun n ->
    if n = 0 then
		(let p = nil 0 in p)
    else
		(let p1 = make_list (n-1) in
		 let p2 = cons n p1 in
		 p2)
		 
let rec reverse =
  fun acc -> fun xs ->
    if fst xs = 0 then acc
    else
    (let x = head xs in
     let xs1 = tail xs in
     let acc1 = cons x acc in
     let r = reverse acc1 xs1 in r);;

let main len = 
  if len > 0 then
    let xs = make_list len in
    let acc = nil 0 in
    let xs1 = reverse acc xs in
    let x = head xs1 in
    ();;

(*
Types:
  main_2115 : unit
  fail_2134 : (x_1:bool[x_1] -> (unit -> unit) -> unit)
  make_list_1037 : (x_1:int ->
                    (x_3:int[x_1 <= 0; x_3 >= 0; x_3 >= 1] -> (int -> (int -> unit) -> unit) -> unit) -> unit)
  reverse_1049 : (x_1:int ->
                  (int -> (int -> unit) -> unit) ->
                  x_8:int[x_8 >= 1; x_1 >= 1] ->
                  (int -> (int[x_1 >= 0] -> unit) -> unit) ->
                  (x_16:int[x_16 >= 1] -> (int -> (int -> unit) -> unit) -> unit) -> unit)
*)
