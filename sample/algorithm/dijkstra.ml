let rec loop () = loop ()
let assume b = if b then () else loop ();;

(* impl of arrays *)
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

let length a = fst a;;

(* impl of lists *)
let nil () = 
    let f () = assume false; (false, (0,0)) in
    (false,f);;

let cons x xs =
    let f = snd xs in
    let b = fst xs in
    let g = fun () -> if Random.bool() then (b,x) else f () in
    (true, g);;

let rec fold n op acc xs =
    let b = fst xs in
    let f = snd xs in
    if b then
        let node = f () in
        let v = snd node in
        let acc1 = op v acc in
        let xs1 = (fst node,f) in
        fold n op acc1 xs1
    else acc;;

(* impl of queues *)
let empty = fun () -> nil ();;
let is_empty = fun q -> not (fst q);;

let push k v queue = cons (k,v) queue;;
let pop queue =
    let b = fst queue in
    let f = snd queue in
    assert b;
    let node = f () in
    (snd node, (fst node, f));;

(* dijkstra's algorithm *)
let rec dijkstra g vis queue =
    let b = is_empty queue in
    if b then ()
    else 
        let p = pop queue in
        let queue1 = snd p in
        let dv = fst p in
        let d = fst dv in
        let v = snd dv in
        let pv = vis () in
        if v = pv then ()
        else
            let vis1 = fun _ -> if Random.bool() then v else vis () in
            let f e acc = 
                let nv = fst e in
                let w = snd e in
                push (d + w) nv acc in
            let queue2 = fold (length g) f queue1 (get g v) in
            dijkstra g vis1 queue2;;

let rec build_sub m i g =
    if i >= m then g
    else 
        let n = length g in
        let v = Random.int(0) in
        let w = Random.int(0) in
        let d = Random.int(0) in
        assume (0 <= v && v < n);
        assume (0 <= w && w < n);
        assume (0 <= d);
        let xs = get g v in
        let xs1 = cons (w,d) xs in
        build_sub m (i + 1) (update g v xs1);;
let build n m = build_sub m 0 (make_array n (nil ()));;

let main n m =
    assume(n > 0);
    let g = build n m in
    let f () = -1 in
    let queue = push 0 0 (empty ()) in
    dijkstra g f queue;;
