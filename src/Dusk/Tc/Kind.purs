module Dusk.Tc.Kind where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Lens (use, (%=), (.=))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Environment (_atTypes)
import Dusk.Tc.Context (_lookupUnsolved, _lookupVariable, _splitAtVariable)
import Dusk.Tc.Context as Context
import Dusk.Tc.Monad (CheckState, _context, _environment, fresh)

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

  t@(Type.Constructor { name }) -> do
    use (_environment <<< _atTypes name) >>= case _ of
      Just k ->
        pure $ t /\ k
      Nothing ->
        throwError "infer: unknown constructor"

  Type.Forall fields@{ ann, name, type_, kind_: mKind } ->
    let
      inferForall :: Type a -> Type a -> m (Type a /\ Type a)
      inferForall kind_' type_' =
        use (_context <<< _splitAtVariable name (Just kind_')) >>= case _ of
          Just { before: context2, after: context3 } -> do
            _context .= context2 <> Context.gatherUnsolved context3
            let
              t = Type.Forall $ fields
                { kind_ = Just kind_'
                , type_ = Context.apply context3 type_'
                }
              k = Type.Constructor
                { ann
                , name: "Type"
                }
            pure $ t /\ k
          Nothing ->
            throwError "infer: could not split context"
    in
      case mKind of
        Just kind_ -> do
          kind_' <- check kind_ (Type.Constructor { ann, name: "Type" })
          _context %= Context.push (Context.Variable name (Just kind_'))
          type_' <- check type_ (Type.Constructor { ann, name: "Type" })
          inferForall kind_' type_'
        Nothing -> do
          name' <- fresh
          let kind_' = Type.Unsolved { ann, name: name' }
          _context %= flip append
            ( Context.fromArray
              [ Context.Unsolved name' $ Just $ Type.Constructor { ann, name: "Type" }
              , Context.Variable name $ Just $ kind_'
              ]
            )
          type_' <- check type_ (Type.Constructor { ann, name: "Type" })
          inferForall kind_' type_'

  t@(Type.Variable { name }) -> do
    use (_context <<< _lookupVariable name) >>= case _ of
      Just { kind_: Just k } ->
        pure $ t /\ k
      _ ->
        throwError "infer: unknown variable"

  t@(Type.Skolem { name }) -> do
    use (_context <<< _lookupVariable name) >>= case _ of
      Just { kind_: Just k } ->
        pure $ t /\ k
      _ ->
        throwError "infer: unknown variable"

  t@(Type.Unsolved { name }) -> do
    use (_context <<< _lookupUnsolved name) >>= case _ of
      Just { kind_: Just k } ->
        pure $ t /\ k
      _ ->
        throwError "infer: unknown unsolved"

  Type.Application { function: t1, argument: t2 } -> do
    (t1' /\ k1') <- infer t1
    context <- use _context
    inferApplication (t1' /\ Context.apply context k1') t2

  Type.KindApplication { ann, function: t1, argument: t2 } -> do
    (t1' /\ k1') <- infer t1
    context <- use _context
    case Context.apply context k1' of
      Type.Forall { name, type_, kind_: Just kind_ } -> do
        t2' <- check t2 kind_

        let
          t1'' = Type.KindApplication { ann, function: t1', argument: t2' }
          t2'' = Type.substituteType name t2' type_

        pure (t1'' /\ t2'')
      _ ->
        throwError "infer: invalid kind application"

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
