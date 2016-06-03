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
		let f = fun j -> fun y -> y in
		(0,f);;

let cons =
	fun x -> fun p ->
		let n = fst p in
		let f = snd p in
		let g = fun j ->
      if j = 0 then x
      else 
        let z = f (j - 1) in
        z
    in
		(n+1,g);;

let rec fold_right =
  fun h -> fun xs -> fun init ->
    if fst xs = 0 then init
    else
      let f = head xs in
      let xs1 = tail xs in
      let g = fold_right h xs1 init in
      let r = h f g in
      r;;

let compose =
  fun f -> fun g -> fun x ->
    let x1 = g x in
    let x2 = f x1 in
    x2;;

let rec make_list =
  fun n ->
    if n = 0 then
      let r = nil 0 in r
    else
       let r = make_list (n - 1) in
       let f = fun m -> n + m in
       let r1 = cons f r in
       r1;;

let main n m = 
  let xs = make_list n in
  let id = fun x -> x in
  let v = fold_right compose xs id m in
  assert (v >= m);;

(* 
Types:
  main_2906 : X
  fail_2926 : (x_2:bool[x_2] -> (unit -> X) -> X)
  fold_right_1492 : (((x_4:int -> (x_6:int[1 <= -x_4 + x_6] -> X) -> X) ->
                      (x_10:int -> (x_12:int[x_12 >= x_10] -> X) -> X) ->
                      x_15:int -> (x_17:int[1 <= -x_15 + x_17] -> X) -> X)
                     ->
                     int ->
                     (int -> ((x_25:int -> (x_27:int[1 <= -x_25 + x_27] -> X) -> X) -> X) -> X) ->
                     (x_33:int -> (x_35:int[x_35 >= x_33] -> X) -> X) ->
                     ((x_40:int -> (x_42:int[1 <= -x_40 + x_42; x_42 >= x_40] -> X) -> X) -> X) -> X)
  make_list_1047 : (x_2:int ->
                    (int[x_2 >= 0] -> (int -> ((x_9:int -> (x_11:int[1 <= -x_9 + x_11] -> X) -> X) -> X) -> X) -> X) ->
                    X)
*)
