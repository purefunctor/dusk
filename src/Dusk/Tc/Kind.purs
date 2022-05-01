module Dusk.Tc.Kind where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Lens (preview, review, use, view, (%=), (.=))
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested (type (/\), (/\))
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Environment (_atTypes)
import Dusk.Tc.Context
  ( Context
  , _lookupUnsolved
  , _lookupVariable
  , _splitAtUnsolved
  , _splitAtVariable
  )
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
        use (_context <<< _splitAtVariable name) >>= case _ of
          Just { before: context2, kind_: Just kind_'', after: context3 }
            | kind_' == kind_'' -> do
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
          _ ->
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

  t1 /\ Type.Forall { ann, name, kind_: mKind, type_ }, t2 ->
    case mKind of
      Just _ -> do
        name' <- fresh
        _context %= Context.push (Context.Unsolved name' mKind)
        let
          t1' = Type.KindApplication
            { ann, function: t1, argument: Type.Unsolved { ann, name: name' } }
          k1' = Type.substituteType name (Type.Unsolved { ann, name: name' }) type_
        inferApplication (t1' /\ k1') t2
      Nothing ->
        throwError "inferApplication: unkinded forall"

  t1 /\ Type.Unsolved { ann, name }, t2 -> do
    u1 <- fresh
    u2 <- fresh
    let
      u1' = Type.Unsolved { ann, name: u1 }
      u2' = Type.Unsolved { ann, name: u2 }
    use (_context <<< _splitAtUnsolved name) >>= case _ of
      Just { before, kind_, after } ->
        let
          middle = Context.fromArray
            [ Context.Unsolved u1 $ Just $ Type.Constructor { ann, name: "Type" }
            , Context.Unsolved u2 $ Just $ Type.Constructor { ann, name: "Type" }
            , Context.Solved name kind_ $ review Type._Function
                { ann0: ann
                , ann1: ann
                , ann2: ann
                , argument: u1'
                , result: u2'
                }
            ]
        in
          _context .= before <> middle <> after
      Nothing ->
        throwError "inferApplication: could not split context"
    t2' <- check t2 u1'
    pure $ Type.Application { ann, function: t1, argument: t2' } /\ u2'

  t1 /\ k1, t2 | Just { argument, result } <- preview Type._Function k1 -> do
    t2' <- check t2 argument
    context <- use _context
    let
      t1' = Type.Application { ann: view Type._ann t1, function: t1, argument: t2' }
      k1' = Context.apply context result
    pure $ t1' /\ k1'

  (_ /\ _), _ ->
    throwError "inferApplication: could not apply kind"

elaborate
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Type a
  -> m (Type a)
elaborate = case _ of

  Type.Constructor { name } -> do
    use (_environment <<< _atTypes name) >>= case _ of
      Just k ->
        pure k
      Nothing ->
        throwError "elaborate: unknown constructor"

  Type.Forall { ann } ->
    pure $ Type.Constructor { ann, name: "Type" }

  Type.Variable { name } ->
    use (_context <<< _lookupVariable name) >>= case _ of
      Just { kind_: Just k } ->
        pure k
      _ ->
        throwError "elaborate: unknown variable"

  Type.Skolem { name } ->
    use (_context <<< _lookupVariable name) >>= case _ of
      Just { kind_: Just k } ->
        pure k
      _ ->
        throwError "elaborate: unknown variable"

  Type.Unsolved { name } ->
    use (_context <<< _lookupUnsolved name) >>= case _ of
      Just { kind_: Just k } ->
        pure k
      _ ->
        throwError "elaborate: unknown unsolved"

  Type.Application { function } -> do
    elaborate function >>= case _ of
      functionKind | Just { result } <- preview Type._Function functionKind ->
        pure result
      _ ->
        throwError "elaborate: must be a function"

  Type.KindApplication { function, argument } -> do
    elaborate function >>= case _ of
      Type.Forall { name, type_ } -> do
        context <- use _context
        pure $ Type.substituteType name (Context.apply context argument) type_
      _ ->
        throwError "elaborate: must be a forall"

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
unify =
  let
    unifyUnsolved :: _ -> _ -> m Unit
    unifyUnsolved u@{ name: a } p1 = do
      -- Δ ⊢ ρ1 ↝ ρ2 ⊣ Θ1, α : ω, Θ2
      p2 <- promote u p1
      use (_context <<< _splitAtUnsolved a) >>= case _ of
        -- Θ1, α : ω, Θ2
        Just { before: theta1, kind_: Just w1, after: theta2 } -> do
          -- Θ1 ⊢ ρ2 : ω2
          _context .= theta1
          w2 <- elaborate p2
          -- Θ1 ⊢ [Θ1] ω1 ≈ ω2 ⊣ Θ3
          unify (Context.apply theta1 w1) w2
          theta3 <- use _context
          -- Θ3, α : ω1 = ρ2, Θ2
          _context .= Context.push (Context.Solved a (Just w1) p2) theta3 <> theta2
        _ ->
          throwError "unify: could not split context"
  in
    case _, _ of
      Type.Application t1, Type.Application t2 -> do
        unify t1.function t2.function
        context <- use _context
        unify (Context.apply context t1.argument) (Context.apply context t2.argument)
      Type.KindApplication t1, Type.KindApplication t2 -> do
        unify t1.function t2.function
        context <- use _context
        unify (Context.apply context t1.argument) (Context.apply context t2.argument)
      t1, t2 | t1 == t2 ->
        pure unit
      Type.Unsolved t1, t2 ->
        unifyUnsolved t1 t2
      t1, Type.Unsolved t2 ->
        unifyUnsolved t2 t1
      _, _ ->
        throwError "unify: could not unify kinds"

promote
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => { ann :: a, name :: Int }
  -> Type a
  -> m (Type a)
promote u@{ ann, name: a } = case _ of

  Type.Unsolved { name: b } ->
    let
      splitContext :: m { context :: Context a, kind_ :: Type a }
      splitContext = do
        use (_context <<< _splitAtUnsolved a) >>= case _ of
          Just { before: context, after } ->
            case Context.lookupUnsolved b after of
              Just { kind_: Just kind_ } ->
                pure { context, kind_ }
              _ ->
                throwError "promote: could not split context"
          _ ->
            throwError "promote: could not split context"
    in
      do
        -- Δ[α][β : ρ]
        { context: delta, kind_: p } <- splitContext
        -- Δ ⊢ ρ ↝ ρ1 ⊢ Θ[α][β : ρ]
        _context .= delta
        p1 <- promote u (Context.apply delta p)
        -- Θ[α][β : ρ]
        { context: theta } <- splitContext
        -- Δ[α][β : ρ] ⊢ β ↝ β1 ⊢ Θ[β1 : ρ1, a][β : ρ = β1]
        b1 <- fresh
        let b1' = Type.Unsolved { ann, name: b1 }
        -- Θ[β1 : ρ1, a][β : ρ = β1]
        _context .= append theta
          ( Context.fromArray
              [ Context.Unsolved b1 (Just p1)
              , Context.Unsolved a Nothing
              , Context.Solved b (Just p1) b1'
              ]
          )
        -- β1
        pure b1'

  t ->
    use (_context <<< _splitAtUnsolved a) >>= case _ of
      Just { before } ->
        Context.wellFormedType before t $> t
      Nothing ->
        throwError "prmote: could not split context"
