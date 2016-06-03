(*
type option = None | Some of int

let rec exists test f n m =
  if n < m
  then
    if test (f n)
    then Some n
    else exists test f (n+1) m
  else
    None

let mult3 n = 3 * n

let main n m =
  let test x = x = m in
    match exists test mult3 0 n with
        None -> ()
      | Some x -> assert (0 <= x && x < n)

*)

let rec exists =
  fun test -> fun f -> fun n -> fun m ->
    if (n < m) then
     let v = f n in
     let b = test v in
     if b then (true,n)
     else
     (let r = exists test f (n+1) m in
      r)
    else
    ((false,-1));;

let main n m = 
  let test = fun x -> x = m in
  let mult3 = fun x -> x + x + x in
  let r = exists test mult3 0 n in
  if fst r then
    assert (0 <= snd r && snd r < n);;

(*
  main_1436 : X
  exists_1161 : ((x_3:int[x_3 >= 0] -> (x_5:bool[x_3 >= 0; x_5] -> X) -> X) ->
                 (x_9:int[x_9 >= 0] -> (x_11:int[x_11 <= 3*x_9 && x_11 >= 0] -> X) -> X) ->
                 x_14:int ->
                 x_15:int[x_14 >= 0] -> (x_17:bool[x_17] -> x_18:int[1 <= x_15 - x_18; x_18 >= 0; (not x_17)] -> X) ->
                 X)
  fail_1448 : (x_2:bool[x_2] -> (unit -> X) -> X)
*)
