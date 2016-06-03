let rec sum =
  fun x -> 
    if x > 0 then
    (let y = sum (x - 1) in x + y)
    else
      (0);;

let main x = 
  let r = sum x in
  assert (r >= x);;

(*
Types:
  main_1151 : X
  fail_1157 : (x_2:bool[x_2] -> (unit -> X) -> X)
  sum_1008 : (x_2:int -> (x_4:int[x_4 >= x_2] -> X) -> X)
*)
