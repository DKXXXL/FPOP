(* Directly copy and modified from 
    https://raw.githubusercontent.com/c-cube/ocaml-containers/master/src/data/CCCache.mli
    
  because we have problem on dynamic linking
*)

(* This file is free software, part of containers. See file "license" for more details. *)

(** Caches Utils

    Particularly useful for memoization. See {!with_cache} and {!with_cache_rec}
    for more details.
    @since 0.6 *)

    type 'a equal = 'a -> 'a -> bool
    type 'a hash = 'a -> int
    
    (** {2 Value interface}
    
        Typical use case: one wants to memoize a function [f : 'a -> 'b]. Code sample:
        {[
          let f x =
            print_endline "call f";
            x + 1;;
    
          let f' = with_cache (lru 256) f;;
          f' 0;;  (* prints *)
          f' 1;;  (* prints *)
          f' 0;;  (* doesn't print, returns cached value *)
        ]}
    
        @since 0.6 *)
    
    type ('a, 'b) t
    
    val clear : (_, _) t -> unit
    (** Clear the content of the cache. *)
    
    type ('a, 'b) callback = in_cache:bool -> 'a -> 'b -> unit
    (** Type of the callback that is called once a cached value is found
        or not.
        Should never raise.
        @param in_cache is [true] if the value was in cache, [false]
          if the value was just produced.
        @since 1.3 *)
    
    val with_cache : ?cb:('a, 'b) callback -> ('a, 'b) t -> ('a -> 'b) -> 'a -> 'b
    (** [with_cache c f] behaves like [f], but caches calls to [f] in the
        cache [c]. It always returns the same value as
        [f x], if [f x] returns, or raise the same exception.
        However, [f] may not be called if [x] is in the cache.
        @param cb called after the value is generated or retrieved. *)
    
    val with_cache_rec :
      ?cb:('a, 'b) callback -> ('a, 'b) t -> (('a -> 'b) -> 'a -> 'b) -> 'a -> 'b
    (** [with_cache_rec c f] is a function that first, applies [f] to
        some [f' = fix f], such that recursive calls to [f'] are cached in [c].
        It is similar to {!with_cache} but with a function that takes as
        first argument its own recursive version.
        Example (memoized Fibonacci function):
        {[
          let fib = with_cache_rec (lru 256)
              (fun fib' n -> match n with
                 | 1 | 2 -> 1
                 | _ -> fib' (n-1) + fib' (n-2)
              );;
    
          fib 70;;
        ]}
        @param cb called after the value is generated or retrieved.
    *)
    
    val size : (_, _) t -> int
    (** Size of the cache (number of entries). At most linear in the number
        of entries. *)
    
    val add : ('a, 'b) t -> 'a -> 'b -> bool
    (** Manually add a cached value. Return [true] if the value has successfully
        been added, and [false] if the value was already bound.
        @since 1.5 *)
    
    val dummy : ('a, 'b) t
    (** Dummy cache, never stores any value. *)
    
    val lru : eq:'a equal -> ?hash:'a hash -> int -> ('a, 'b) t
    (** LRU cache of the given size ("Least Recently Used": keys that have not been
        used recently are deleted first). Never grows wider than the given size. *)

    val with_cache_rec2 : ([ `Left of 'a | `Right of 'c ], [ `Left of 'b | `Right of 'd ]) t ->
      (('a -> 'b) -> ('c -> 'd) -> 'a -> 'b) ->
      (('a -> 'b) -> ('c -> 'd) -> 'c -> 'd) -> ('a -> 'b) * ('c -> 'd)