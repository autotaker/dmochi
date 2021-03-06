let make_array n i = i

let rec array_max n i a =
  if i >= n
  then 0
  else
    let x = a i in
    let y = array_max n (i+1) a in
      if x > y then x else y

let rec check n i max a =
  if i >= n
  then ()
  else
    begin
      assert (a i <= max);
      check n (i+1) max a
    end

let main n =
  let array = make_array n in
  let max = array_max n 0 array in
  check n 0 max array
