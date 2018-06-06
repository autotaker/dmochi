let rec update i a x = 
    let a j = if i=j then x else a j in a

let queen size =
  assume (size > 0);
  let queenArray = fun i -> 0 in
  let assign i j queenArray = update (i) queenArray j in
  let rec loop row queenArray =
    let next = queenArray(row) + 1 in
    if next > size then
      let queenArray = update row queenArray 0 in
      if row = 0 then () else loop (row-1) queenArray
    else
      let queenArray = update row queenArray next in
      if Random.bool() then
        if (row+1) = size then begin 
            let rec aux1 row1 = begin
                if row1 = size then () else
                    begin
                        let n = if row1 = row then next else queenArray row1 in
                        assert (0 <= row1 && row1 <= size);
                        aux1 (row1 + 1)
                    end
            end
            in aux1(0);
            loop(row) queenArray 
        end else 
            loop(row+1) queenArray
      else loop row queenArray
  in loop(0) queenArray
