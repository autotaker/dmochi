let get array idx =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx && idx < n );
    f ();;

let make_array = 
    fun size a -> let f _ = a in (size, f);;

let update array idx value =
    let n = fst array in
    let f = snd array in
    assert( 0 <= idx && idx < n );
    let g = fun () -> if Random.bool() then value else f () in
    (n, g);;

let rec dfs g v vis =
    let pv = vis () in
    if v = pv then ()
    else
        let nv = get g v in
        let vis1 = fun _ -> if Random.bool() then v else vis () in
        dfs g nv vis1;;

let rec loop () = loop ()
let assume b = if b then () else loop ();;

let rec build_sub n i g =
    if i >= n then g
    else 
        let v = Random.int(0) in
        assume (0 <= v && v < n);
        build_sub n (i + 1) (update g i v);;
let build n = build_sub n 0 (make_array n 0);;

let main n =
    assume(n > 0);
    let g = build n in
    let f () = -1 in
    dfs g 0 f;;

