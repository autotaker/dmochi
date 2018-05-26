
let make_array n s i = assert (0 <= i && i < n); s
let kmpMatch u =
  let plen = 3 in
  let shiftArray0 = make_array plen (-1) in
  let rec loopShift i j shiftArray1 =
    if j = 3 then shiftArray1 else
        let shiftArray2 = if i+1 < j then shiftArray1 else shiftArray1 in
          loopShift (shiftArray1 j) (j+1) shiftArray2
  in
  let shiftArray3 = loopShift (-1) 1 shiftArray0 in
  ()

let main u = kmpMatch ()
