-- | This module defines a state monad implemented in terms of uncurried
-- | functions and continuation-passing style, similar in vein to the
-- | `uncurried-transformers` library. Instead of hiding the final
-- | result type behind the constructor, this implementation exposes it
-- | as a type parameter instead.
module Uncurried.StateC where

import Prelude

import Data.Function.Uncurried (Fn2, mkFn2, runFn2)
import Data.Newtype (class Newtype)

newtype StateC r s a = StateC (Fn2 s (Fn2 s a r) r)

derive instance Newtype (StateC r s a) _

instance Functor (StateC r s) where
  map f (StateC t1) = StateC
    ( mkFn2 \state next ->
        runFn2 t1 state
          ( mkFn2 \state' a ->
              runFn2 next state' (f a)
          )
    )

instance Apply (StateC r s) where
  apply (StateC t1) (StateC t2) = StateC
    ( mkFn2 \state next ->
        runFn2 t1 state
          ( mkFn2 \state' f ->
              runFn2 t2 state'
                ( mkFn2 \state'' a ->
                    runFn2 next state'' (f a)
                )
          )
    )

instance Applicative (StateC r s) where
  pure a = StateC
    ( mkFn2 \state next ->
        runFn2 next state a
    )

instance Bind (StateC r s) where
  bind (StateC t1) k = StateC
    ( mkFn2 \state next ->
        runFn2 t1 state
          ( mkFn2 \state' result -> do
              let (StateC t2) = k result
              runFn2 t2 state' next
          )
    )

instance Monad (StateC r s)
