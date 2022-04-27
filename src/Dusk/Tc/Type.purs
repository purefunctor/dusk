module Dusk.Tc.Type where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState, gets)
import Data.Lens (preview)
import Data.Maybe (Maybe(..), isNothing)
import Data.Traversable (traverse_)
import Dusk.Ast.Expr (Expr)
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Tc.Context as Context
import Dusk.Tc.Monad (CheckState, fresh, withTypeVariableInContext, withUnsolvedTypeInContext)
import Partial.Unsafe (unsafeCrashWith)

subsumes
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Eq a
  => Type a
  -> Type a
  -> m Unit
subsumes = case _, _ of
  -- Functions are contravariant in their arguments and covariant in their
  -- results i.e. when a function `f` is a subtype of another `g`, its argument
  -- type is more general while its result type is more specific. This means
  -- that in places where `g` is used, `f` would still work in that it doesn't
  -- require more for its arguments nor does it return less for its results.
  t1, t2
    | Just f1 <- preview Type._Function t1
    , Just f2 <- preview Type._Function t2 -> do
        subsumes f2.argument f1.argument
        context <- gets _.context
        subsumes (Context.apply context f1.result) (Context.apply context f2.result)

  t1, Type.Forall { ann, name, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' $ subsumes t1 t2

  Type.Forall { ann, name, type_ }, t2 -> do
    name' <- fresh
    let t1 = Type.substituteType name (Type.Unsolved { ann, name: name' }) type_
    withUnsolvedTypeInContext name' $ subsumes t1 t2

  t1, t2 ->
    unify t1 t2

unify
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Type a
  -> m Unit
unify = case _, _ of
  Type.Forall f1, Type.Forall f2 -> do
    name' <- append "t" <<< show <$> fresh
    let
      t1 = Type.substituteType f1.name (Type.Skolem { ann: f1.ann, name: name' }) f1.type_
      t2 = Type.substituteType f2.name (Type.Skolem { ann: f2.ann, name: name' }) f2.type_
    withTypeVariableInContext name' $ unify t1 t2

  t1, Type.Forall { ann, name, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' $ unify t1 t2

  Type.Forall { ann, name, type_ }, t2 -> do
    name' <- append "t" <<< show <$> fresh
    let t1 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' $ unify t1 t2

  Type.Variable f1, Type.Variable f2
    | f1.name == f2.name -> variableInScopeCheck f1.name

  Type.Skolem f1, Type.Skolem f2
    | f1.name == f2.name -> variableInScopeCheck f1.name

  Type.Unsolved f1, Type.Unsolved f2
    | f1.name == f2.name -> unsolvedInScopeCheck f1.name

  t1, Type.Unsolved f2 -> do
    unsolvedInScopeCheck f2.name
    occursCheck f2.name t1
    solve f2.name t1

  Type.Unsolved f1, t2 -> do
    unsolvedInScopeCheck f1.name
    occursCheck f1.name t2
    solve f1.name t2

  Type.Constructor f1, Type.Constructor f2
    | f1.name == f2.name ->
        pure unit

  Type.Application f1, Type.Application f2 -> do
    unify f1.function f2.function
    unify f1.argument f2.argument

  Type.KindApplication f1, Type.KindApplication f2 -> do
    unify f1.function f2.function
    unify f1.argument f2.argument

  _, _ ->
    throwError "unify: could not unify types"
  where
  variableInScopeCheck :: String -> m Unit
  variableInScopeCheck name = do
    context <- gets _.context
    when (isNothing $ Context.lookupVariable name context) do
      throwError "unify: variable not in scope"

  unsolvedInScopeCheck :: Int -> m Unit
  unsolvedInScopeCheck name = do
    context <- gets _.context
    when (isNothing $ Context.lookupUnsolved name context) do
      throwError "unify: variable not in scope"

  occursCheck :: Int -> Type a -> m Unit
  occursCheck n = go
    where
    go = case _ of
      Type.Forall { kind_, type_ } -> do
        traverse_ go kind_
        go type_
      Type.Variable _ ->
        pure unit
      Type.Skolem _ ->
        pure unit
      Type.Unsolved { name } ->
        if n == name then
          throwError "unify: occurs check"
        else
          pure unit
      Type.Constructor _ ->
        pure unit
      Type.Application { function, argument } -> do
        go function
        go argument
      Type.KindApplication { function, argument } -> do
        go function
        go argument

solve :: forall a m. MonadState (CheckState a) m => MonadError String m => Int -> Type a -> m Unit
solve _ = case _ of
  Type.Forall _ ->
    throwError "solve: impredicativity error"
  _ ->
    pure unit

check
  :: forall a m. MonadState (CheckState a) m => MonadError String m => Expr a -> Type a -> m Unit
check _ _ = pure unit

infer :: forall a m. MonadState (CheckState a) m => MonadError String m => Expr a -> m (Type a)
infer _ = unsafeCrashWith "infer: unimplemented"

inferApplication
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> Expr a
  -> m (Type a)
inferApplication _ _ = unsafeCrashWith "inferApplication: unimplemented"
