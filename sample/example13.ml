
let make_array n s i = assert (0 <= i); s
let kmpMatch slen str plen pat =
  let rec loop s p =
    assume(p < plen);
    assume(s < slen);
    str s;
    pat p;
    0
  in loop 0 0

let main n a m b =
  let array1 = make_array n a in
  let array2 = make_array m b in
  assume(n > 0 && m > 0);
  kmpMatch n array1 m array2; 
  ()
