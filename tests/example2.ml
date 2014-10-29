let rec is_zero_div (x_zero,x_pos) (y_zero,y_pos) =
  if y_zero
  then Fail 
  else if x_zero 
    then true
    else true <> false
and is_pos_div (x_zero,x_pos) (y_zero,y_pos) =
  if y_zero then 
    Fail 
  else if y_pos then
    if x_zero then
      false
    else if x_pos then
      true <> false
    else
      false
  else
    if x_zero then
      false
    else if x_pos then
      false
    else
      true <> false
and is_pos (x_zero,x_pos) = x_pos
and is_zero (x_zero,x_pos) = x_zero
and is_zero_succ (x_zero,x_pos) = 
  if x_zero then
    false
  else if x_pos then
    false
  else true <> false
and is_pos_succ (x_zero,x_pos) =
  if x_zero then
    true
  else if x_pos then
    true
  else
    true <> false
and validate (x_zero,x_pos) =
  if x_zero then
    if x_pos then Omega else true
  else true
in
(fun (x_zero,x_pos) (y_zero,y_pos) ->
  if validate (x_zero,x_pos) then
    if validate (y_zero,y_pos) then
      if is_zero (y_zero,y_pos) then
        (fun (y1_zero,y1_pos) ->
          if validate (y1_zero,y1_pos) then
            is_zero_div (x_zero,x_pos) (y1_zero,y1_pos)
          else Omega) (is_zero_succ (y_zero,y_pos),is_pos_succ (y_zero,y_pos))
      else Omega
    else Omega
  else Omega) (true <> false,true <> false) (true <> false,true <> false)
