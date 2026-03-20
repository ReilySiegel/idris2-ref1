module Data.Linear.Rendezvous

import public Data.Linear.Token
import Data.Linear.Ref1
import Data.Linear.Unique

%default total

--------------------------------------------------------------------------------
-- Rendezvous
--------------------------------------------------------------------------------

-- internal state of a `Rendezvous` value
data ST : Type -> Type -> Type where
  Ini : ST s a
  Put : a -> ST s a
  Obs : (cb : a -> F1' s) -> ST s a
  Fin : ST s a

||| An atomic, thread-safe meeting point between two 'threads' of execution, to
||| pass a value exactly once.
export
record Rendezvous s a where
  constructor R
  ref : Ref s (ST s a)

||| Creates a new `Rendezvous`.
export %inline
rendezvous1 : F1 s (Rendezvous s a)
rendezvous1 t = let ref # t := ref1 Ini t in R ref # t

||| Convenience alias of `rendezvous1`, which takes the type of
||| the value stored as an explicit argument.
export %inline
rendezvousOf1 : (0 a : _) -> F1 s (Rendezvous s a)
rendezvousOf1 _ = rendezvous1


||| Attempts to put a value to a `Rendezvous` and close it.
|||
||| Returns `True` if the put was successful, or `False` if the Rendezvous is
||| closed or already has a competing put.
export
putRendezvous1 : Rendezvous s a -> (v : a) -> F1 s Bool
putRendezvous1 r@(R ref) v t =
  assert_total $ let x # t := read1 ref t in go x x t
  where
    go : ST s a -> ST s a -> F1 s Bool
    go x Ini t =
      case caswrite1 ref x (Put v) t of
        True # t => True # t
        _    # t => putRendezvous1 r v t
    go x (Put _)  t = False # t
    go x (Obs cb) t =
      case caswrite1 ref x Fin t of
        True # t => let _ # t := cb v t in True # t
        _    # t => putRendezvous1 r v t
    go x Fin t = False # t

||| Removes an observation from a `Rendezvous`, and closes it so that a value
||| may never be put.
unobs1 : Rendezvous s a -> F1' s
unobs1 r@(R ref) t =
  assert_total $ let x # t := read1 ref t in go x x t
  where
    go : ST s a -> ST s a -> F1' s
    go x (Obs cb) t =
      case caswrite1 ref x Fin t of
        True # t => () # t
        _    # t => unobs1 r t
    go _ _ t = () # t

||| Observe a `Rendezvous` by installing a callback.
|||
||| The callback is invoked immediately in case the value has already been set,
||| or the `Rendezvous` is already closed.
|||
||| The action that is returned by this function can be used to unregister the
||| observer and close the `Rendezvous`.
export
observeRendezvous1 : Rendezvous s a -> (a -> F1' s) -> F1 s (F1' s)
observeRendezvous1 r@(R ref) cb t =
  assert_total $ let x # t := read1 ref t in go x x t
  where
    go : ST s a -> ST s a -> F1 s (F1' s)
    go x (Put v) t = case caswrite1 ref x Fin t of
      True # t => let _ # t := cb v t in unit1 # t
      _    # t => observeRendezvous1 r cb t

    go x Ini t =
      case caswrite1 ref x (Obs cb) t of
        True # t => unobs1 r # t
        _    # t => observeRendezvous1 r cb t

    go _ _ t = unit1 # t

--------------------------------------------------------------------------------
-- Lift1 Utilities
--------------------------------------------------------------------------------

||| Lifted version of `rendezvous1`
export %inline
rendezvous : Lift1 s f => f (Rendezvous s a)
rendezvous = lift1 rendezvous1

||| Lifted version of `rendezvousOf`
export %inline
rendezvousOf : Lift1 s f => (0 a : _) -> f (Rendezvous s a)
rendezvousOf _ = rendezvous

||| Lifted version of `putRendezvous1`
export %inline
putRendezvous : Lift1 s f => Rendezvous s a -> (v : a) -> f Bool
putRendezvous o v = lift1 $ putRendezvous1 o v
