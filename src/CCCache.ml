(* Directly copy and modified from 
  https://raw.githubusercontent.com/c-cube/ocaml-containers/master/src/data/CCCache.ml
  
  because we have problem on dynamic linking.
*)
open Utils

(* This file is free software, part of containers. See file "license" for more details. *)

(** {1 Caches} *)

type 'a equal = 'a -> 'a -> bool
type 'a hash = 'a -> int

let default_hash_ = Hashtbl.hash

(** {2 Value interface} *)

type ('a, 'b) t = {
  set: 'a -> 'b -> unit;
  get: 'a -> 'b; (* or raise Not_found *)
  size: unit -> int;
  clear: unit -> unit;
}
(** Invariants:
    - after [cache.set x y], [get cache x] must return [y] or raise [Not_found]
    - [cache.set x y] is only called if [get cache x] fails, never if [x] is already bound
    - [cache.size()] must be positive and correspond to the number of items in [cache.iter]
    - [cache.iter f] calls [f x y] with every [x] such that [cache.get x = y]
    - after [cache.clear()], [cache.get x] fails for every [x]
*)

type ('a, 'b) callback = in_cache:bool -> 'a -> 'b -> unit

let clear c = c.clear ()

let add c x y =
  try
    (* check that x is not bound (see invariants) *)
    let _ = c.get x in
    false
  with Not_found ->
    c.set x y;
    true

let default_callback_ ~in_cache:_ _ _ = ()

let with_cache ?(cb = default_callback_) c f x =
  try
    let y = c.get x in
    cb ~in_cache:true x y;
    y
  with Not_found ->
    let y = f x in
    c.set x y;
    cb ~in_cache:false x y;
    y

let with_cache_rec ?(cb = default_callback_) c f =
  let rec f' x = with_cache ~cb c (f f') x in
  f'

let size c = c.size ()

let dummy =
  {
    set = (fun _ _ -> ());
    get = (fun _ -> raise Not_found);
    clear = (fun _ -> ());
    size = (fun _ -> 0);
  }


module type ContentTy = sig
  type t

end


module LRU (X:ContentTy) = struct
  (* We use two  *)
  module MapX = Map.Make(
    struct type t = X.t 
    let compare x y = Stdlib.compare x y 
  end)

  type timestamp = int
  module Maptime = Map.Make(
    struct
       type t = timestamp
       let compare = Stdlib.compare
    end
  )

  
  (* t represents the state of one LRU cache *)
  type 'v tct = { 
    contents : (timestamp * 'v) MapX.t ;
    freq : X.t Maptime.t;
    oldest : timestamp;
    size : int;
    capacity : int;
    new_timestamp : unit -> timestamp;
  } 
  



  let next_timestamp : timestamp -> timestamp = fun x -> x + 1

  type 'v t = 'v tct ref 

  let make_new (capacity : int) : 'v tct = 
    let oldest = 0 in 
    let size = 0 in 
    let new_timestamp = 
      let time = Summary.ref ~name:(Utils.fresh_string ~prefix:"TimeCounter" ()) oldest in 
      let tik () = (time := (!time) + 1; !time) in 
      tik
    in
    let contents = MapX.empty in 
    let freq =  Maptime.empty in 
    {contents; freq; new_timestamp; oldest; size; capacity}

  let get (c : 'v t) (key : X.t) : 'v = 
    let current_c = !c in 
    if MapX.mem key current_c.contents then () else raise Not_found;
    (* then we update the freq *)
    let (last_appear, res) = MapX.find key current_c.contents in 
    let new_freq = 
      Maptime.add (current_c.new_timestamp ()) key @@
      Maptime.remove last_appear current_c.freq in 
    let new_c = {current_c with freq = new_freq} in
    c := new_c; 
    res
    

  let remove_oldest (c : 'v t) : unit = 
    if !c.size <= 0 then raise @@ Stdlib.Failure "Cache is Empty!" else ();
    let current_c = !c in 
    let timestamp_to_remove = 
      let oldstamp = ref current_c.oldest in 
      let rec until_found () =
        if Maptime.mem !oldstamp current_c.freq 
          then !oldstamp 
          else (oldstamp := next_timestamp !oldstamp; until_found ()) in 
      until_found () in 
    let key_to_remove = Maptime.find timestamp_to_remove current_c.freq in 
    let new_freq = Maptime.remove timestamp_to_remove current_c.freq in 
    let new_contents = MapX.remove key_to_remove current_c.contents in 
    let new_size = current_c.size - 1 in 
    let new_c = {current_c with contents = new_contents; freq = new_freq; size = new_size; oldest = timestamp_to_remove} in 
    c := new_c  
  let add_new (c : 'v t) (key : X.t) (value : 'v) : unit = 
    if !c.size >= !c.capacity then raise @@ Stdlib.Failure "Cache is Full!" else ();
    let current_c = !c in 
    let new_timestamp = current_c.new_timestamp() in 
    let new_freq = Maptime.add new_timestamp key current_c.freq in 
    let new_contents = MapX.add key (new_timestamp, value) current_c.contents in 
    let new_size = current_c.size + 1 in 
    let new_c = {current_c with freq = new_freq; contents = new_contents; size = new_size} in 
    c := new_c 
  
  let set (c : 'v t) (key : X.t) (value : 'v) : unit = 
    if !c.size > !c.capacity then raise @@ Stdlib.Failure "Breaking Invariance!" else ();
    if !c.size = !c.capacity then remove_oldest c else ();
    add_new c key (value) 


  let clear (c : 'v t) : unit = 
    let capacity = !c.capacity in 
    c := make_new capacity 

  let size (c : 'v t) () = 
    !c.size

  let make capacity = Summary.ref ~name:(Utils.fresh_string  ~prefix:"Cache" ()) @@ make_new capacity
end



let lru (type a) ~eq ?(hash = default_hash_) size =
  let module L = LRU (struct
    type t = a
  end) in
  let c = L.make size in
  {
    get = (fun x -> L.get c x);
    set = (fun x y -> L.set c x y);
    clear = (fun () -> L.clear c);
    size = L.size c;
  }




(* Strengthen the with_rec, for open mutual rcursive function *)
let with_cache_rec2 h 
    (f1 : ('a -> 'b) -> ('c -> 'd) -> ('a -> 'b)) 
    (f2 : ('a -> 'b) -> ('c -> 'd) -> ('c -> 'd)) : 
    ('a -> 'b) * ('c -> 'd)
    = 
  let fss (fs : ([`Left of 'a | `Right of 'c] -> [`Left of 'b | `Right of 'd]) ) (ac : [`Left of 'a | `Right of 'c]) : [`Left of 'b | `Right of 'd] = 
      let cf1 (a : 'a) : 'b = 
        begin match (fs (`Left a)) with 
        | `Left  b -> b 
        | _ -> cerror ~einfo:__LOC__ () 
        end in 
      let cf2 (c : 'c) : 'd = 
        begin match (fs (`Right c)) with 
        | `Right  d -> d 
        | _ -> cerror ~einfo:__LOC__ () 
        end in
      match ac with 
      | `Left a -> `Left  (f1 cf1 cf2 a) 
      | `Right c -> `Right (f2 cf1 cf2 c) 
      in
  (* let open CCCache in  *)
  let closed_rec =  with_cache_rec h fss in 
  let cf1 x = 
    match closed_rec (`Left x) with 
    | `Left y -> y 
    | _ -> cerror ~einfo:__LOC__ ()  in 
  let cf2 x = 
    match closed_rec (`Right x) with 
    | `Right y -> y 
    | _ -> cerror ~einfo:__LOC__ ()  in 
  (cf1, cf2)



