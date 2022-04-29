module Dusk.Tc.Kind where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Dusk.Ast.Type (Type)
import Dusk.Tc.Monad (CheckState)

instantiate
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => { type_ :: Type a, kind_ :: Type a }
  -> Type a
  -> m (Type a)
instantiate = case _, _ of
  _, _ ->
    throwError "instantiate: not implemented"

check
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Type a
  -> m (Type a)
check = case _, _ of
  _, _ ->
    throwError "check: not implemented"

infer
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> m { type_ :: Type a, kind_ :: Type a }
infer = case _ of
  _ ->
    throwError "infer: not implemented"

inferApplication
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => { type_ :: Type a, kind_ :: Type a }
  -> Type a
  -> m { type_ :: Type a, kind_ :: Type a }
inferApplication = case _, _ of
  _, _ ->
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
