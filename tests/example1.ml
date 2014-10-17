let rec g y = fun z -> fun x -> z x <> y x
and     f1 x = if x then x else Omega
and     f2 x = if x then Omega else x
and     f3 x = Omega
in (fun f ->
  if f true 
    then if f false 
      then Fail
      else g f3 f3 Fail
    else Fail) (g f1 f2)
