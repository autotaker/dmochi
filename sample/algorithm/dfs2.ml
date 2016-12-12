
let rec loop () = loop ()
let assume b = if b then () else loop ();;

let get array idx =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx );
    f ();;

let make_array = 
    fun size a -> let f _ = a in (size, f);;

let update array idx value =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx );
    let g = fun () -> if Random.bool() then value else f () in
    (n, g);;

let length a = fst a;;

let nil () = 
    let f () = assume false; (false, 0) in
    (false,f);;

let cons x xs =
    let f = snd xs in
    let b = fst xs in
    let g = fun () -> if Random.bool() then (b,x) else f () in
    (true, g);;

let rec iter n action xs =
    let b = fst xs in
    let f = snd xs in
    if b then
        let node = f () in
        let v = snd node in
        action v;
        let xs1 = (fst node,f) in
        iter n action xs1
    else ();;

let rec dfs g v vis =
    let pv = vis () in
    if v = pv then ()
    else
        let vis1 = fun _ -> if Random.bool() then v else vis () in
        let f nv = dfs n g nv vis1 in
        iter f (get g v);;

let rec build_sub m i g =
    if i >= m then g
    else 
        let v = Random.int(0) in
        let w = Random.int(0) in
        assume (0 <= v);
        assume (0 <= w);
        let xs = get g v in
        let xs1 = cons w xs in
        build_sub m (i + 1) (update g v xs1);;
let build n m = build_sub m 0 (make_array n (nil ()));;

let main n m =
    assume(n > 0);
    let g = build n m in
    let f () = -1 in
    dfs g 0 f;;

