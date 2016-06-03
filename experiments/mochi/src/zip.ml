
(*
let rec zip (xs:int list) (ys:int list) =
  match xs with
      [] ->
        begin
          match ys with
              [] -> []
            | _ -> assert false
        end
    | x::xs' ->
        match ys with
            [] -> assert false
          | y::ys' -> (x,y)::zip xs' ys'

let rec make_list n =
  if n < 0
  then []
  else n :: make_list (n-1)

let main n =
  let xs = make_list n in
    zip xs xs

*)

let head_pair =
	fun p -> 
		let f = snd p in
		let z = f 0 in
		z;;

let head_int =
	fun p -> 
		let f = snd p in
		let z = f 0 in
		z;;
		
let tail_pair =
	fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j -> let v = f (j + 1) in v in
		(n-1,g)

let tail_int =
	fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j -> let v = f (j + 1) in v in
		(n-1,g)

let nil_int =
	fun n -> 
		let f = fun j -> 0 in
    (0,f);;

let nil_pair =
	fun n -> 
		let f = fun j -> (0,0) in
    (0,f);;

let cons_int =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
      if j = 0 then
        x
      else 
			(let z = f (j - 1) in z) in
		(n+1,g);;

let cons_pair =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
      if j = 0 then
        x
      else 
			(let z = f (j - 1) in z) in
		(n+1,g);;

let rec zip =
  fun xs -> fun ys ->
    if fst xs = 0 then
    (if fst ys = 0 then
      (let r = nil_pair 0 in r)
     else
       assert false)
    else
    (let x = head_int xs in
     let xs1 = tail_int xs in
     if fst ys = 0 then
       assert false
     else
     (let y = head_int ys in
      let ys1 = tail_int ys in
      let rs1 = zip xs1 ys1 in
      let rs = cons_pair (x,y) rs1 in
      rs));;
      
let rec make_list =
  fun n ->
    if n < 0 then
    (let r = nil_int 0 in r)
    else
    (let r = make_list (n - 1) in
     let z = cons_int n r in
     z);;

let main n =
let xs = make_list n in
let ps = zip xs xs in
()

(*
Types:
  main_3203 : unit
  fail_3228 : (x_1:bool[x_1] -> (unit -> unit) -> unit)
  fail_3229 : (x_1:bool[x_1] -> (unit -> unit) -> unit)
  head_int_1631 : (int -> (int -> (int -> unit) -> unit) -> (int -> unit) -> unit)
  make_list_1086 : (int -> (x_3:int[x_3 = 0; x_3 = 1] -> (int -> (int -> unit) -> unit) -> unit) -> unit)
  tail_int_1628 : (x_1:int[x_1 = 1] ->
                   (int -> (int -> unit) -> unit) ->
                   (x_9:int[x_1 = x_9 + 1; x_9 = 0] -> (int -> (int -> unit) -> unit) -> unit) -> unit)
  zip_1076 : (x_1:int ->
              (int -> (int -> unit) -> unit) ->
              x_8:int[x_1 = 0; x_1 = 1; x_1 = x_8] ->
              (int -> (int -> unit) -> unit) -> (int -> (int -> (int -> int -> unit) -> unit) -> unit) -> unit)
*)
  

