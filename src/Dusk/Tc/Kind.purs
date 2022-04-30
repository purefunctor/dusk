module Dusk.Tc.Kind where

import Data.Lens
import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Tuple.Nested (type (/\), (/\))
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Tc.Context as Context
import Dusk.Tc.Monad (CheckState, _context, fresh)

instantiate
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => (Type a /\ Type a)
  -> Type a
  -> m (Type a)
instantiate = case _, _ of
  t1 /\ Type.Forall { ann, name, type_, kind_ }, k2
    -- `k2` has to be monokinded, otherwise, we subsume.
    | Type.isMonoType k2 -> do
        name' <- fresh

        let
          unsolved = Type.Unsolved { ann, name: name' }
          t1' = Type.KindApplication { ann, function: t1, argument: unsolved }
          k1' = Type.substituteType name unsolved type_

        _context %= Context.push (Context.Unsolved name' kind_)

        instantiate (t1' /\ k1') k2

  t1 /\ k1, k2 ->
    subsumes k1 k2 $> t1

check
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Type a
  -> m (Type a)
check t1 k1 = do
  t2 /\ k2 <- infer t1
  context <- use _context
  instantiate (t2 /\ Context.apply context k2) (Context.apply context k1)

infer
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> m (Type a /\ Type a)
infer = case _ of
  _ ->
    throwError "infer: not implemented"

inferApplication
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => (Type a /\ Type a)
  -> Type a
  -> m (Type a /\ Type a)
inferApplication = case _, _ of
  (_ /\ _), _ ->
    throwError "inferApplication: not implemented"

elaborate
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> m (Type a)
elaborate = case _ of
  _ ->
    throwError "elaborate: not implemented"

subsumes
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Type a
  -> m Unit
subsumes = case _, _ of
  _, _ ->
    throwError "subsumes: not implemented"

unify
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Type a
  -> m Unit
unify = case _, _ of
  _, _ ->
    throwError "subsumes: not implemented"

promote
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Int
  -> Type a
  -> m (Type a)
promote _ = case _ of
  _ ->
    throwError "promote: not implemented"
