module Dusk.Tc.Type where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Lens (preview, review, use, view, (%=), (.=))
import Data.Maybe (Maybe(..), isNothing)
import Data.Traversable (traverse_)
import Dusk.Ast.Ann (From(..))
import Dusk.Ast.Expr (Expr)
import Dusk.Ast.Expr as Expr
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Environment (_atNames)
import Dusk.Tc.Context as Context
import Dusk.Tc.Monad
  ( CheckState
  , _context
  , _environment
  , fresh
  , splitContextAtUnsolved
  , withNameInEnvironment
  , withTypeVariableInContext
  , withUnsolvedTypeInContext
  )

subsumes
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Type From
  -> Type From
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
        context <- use _context
        subsumes (Context.apply context f1.result) (Context.apply context f2.result)

  t1, Type.Forall { ann, name, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann: FromDerived ann, name: name' }) type_
    withTypeVariableInContext name' Nothing $ subsumes t1 t2

  Type.Forall { ann, name, type_ }, t2 -> do
    name' <- fresh
    let t1 = Type.substituteType name (Type.Unsolved { ann: FromDerived ann, name: name' }) type_
    withUnsolvedTypeInContext name' Nothing $ subsumes t1 t2

  t1, t2 ->
    unify t1 t2

unify
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Type From
  -> Type From
  -> m Unit
unify = case _, _ of

  Type.Forall f1, Type.Forall f2 -> do
    name' <- append "t" <<< show <$> fresh
    let
      t1 = Type.substituteType f1.name (Type.Skolem { ann: FromDerived f1.ann, name: name' })
        f1.type_
      t2 = Type.substituteType f2.name (Type.Skolem { ann: FromDerived f2.ann, name: name' })
        f2.type_
    withTypeVariableInContext name' Nothing $ unify t1 t2

  t1, Type.Forall { ann, name, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann: FromDerived ann, name: name' }) type_
    withTypeVariableInContext name' Nothing $ unify t1 t2

  Type.Forall { ann, name, type_ }, t2 -> do
    name' <- append "t" <<< show <$> fresh
    let t1 = Type.substituteType name (Type.Skolem { ann: FromDerived ann, name: name' }) type_
    withTypeVariableInContext name' Nothing $ unify t1 t2

  Type.Variable f1, Type.Variable f2
    | f1.name == f2.name -> variableInScopeCheck f1.name

  Type.Skolem f1, Type.Skolem f2
    | f1.name == f2.name -> variableInScopeCheck f1.name

  Type.Unsolved f1, Type.Unsolved f2
    | f1.name == f2.name -> unsolvedInScopeCheck f1.name

  t1, Type.Unsolved f2 -> do
    unsolvedInScopeCheck f2.name
    occursCheck f2.name t1
    solve f2 t1

  Type.Unsolved f1, t2 -> do
    unsolvedInScopeCheck f1.name
    occursCheck f1.name t2
    solve f1 t2

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
    context <- use _context
    when (isNothing $ Context.lookupVariable name context) do
      throwError "unify: variable not in scope"

  unsolvedInScopeCheck :: Int -> m Unit
  unsolvedInScopeCheck name = do
    context <- use _context
    when (isNothing $ Context.lookupUnsolved name context) do
      throwError "unify: unsolved not in scope"

  occursCheck :: Int -> Type From -> m Unit
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

solve
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => { ann :: From, name :: Int }
  -> Type From
  -> m Unit
solve u@{ name: a } t = do
  contexts <- splitContextAtUnsolved a

  let
    -- Γ[a^] ⊢ Γ[a^ = t]
    insertToContext m = do
      Context.wellFormedType contexts.before m
      _context .= Context.push (Context.Solved a Nothing m) contexts.before <> contexts.after

  case t of

    Type.Forall _ -> do
      throwError "solve: impredicativity error"

    Type.Variable _ ->
      insertToContext t

    Type.Skolem _ ->
      insertToContext t

    Type.Unsolved { name: b } -> do
      case Context.splitAtUnsolved b contexts.after of
        -- Γ[a^][b^] ⊢ Γ[a^][b^ = a^]
        Just contexts' ->
          let
            context = Context.push (Context.Unsolved a Nothing) contexts.before
              <> contexts.after
            context' = Context.push (Context.Solved b Nothing $ Type.Unsolved u) contexts'.before
              <> contexts'.after
          in
            _context .= context <> context'
        Nothing ->
          insertToContext t

    Type.Constructor _ ->
      insertToContext t

    _ | Just f <- preview Type._Function t -> do
      u1 <- fresh
      u2 <- fresh

      let
        a1 = { ann: FromDerived f.ann0, name: u1 }
        a2 = { ann: FromDerived f.ann1, name: u2 }
        between = Context.fromArray
          [ Context.Unsolved u2 Nothing
          , Context.Unsolved u1 Nothing
          , Context.Solved a Nothing
              $ review Type._Function
              $ f
                  { argument = Type.Unsolved a1
                  , result = Type.Unsolved a2
                  }
          ]

      _context .= contexts.before <> between <> contexts.after
      solve a1 f.argument

      contextN <- use _context
      solve a2 (Context.apply contextN f.result)

    Type.Application { ann, function, argument } -> do
      u1 <- fresh
      u2 <- fresh

      let
        a1 = { ann: FromDerived $ view Type._ann function, name: u1 }
        a2 = { ann: FromDerived $ view Type._ann argument, name: u2 }
        between = Context.fromArray
          [ Context.Unsolved u2 Nothing
          , Context.Unsolved u1 Nothing
          , Context.Solved a Nothing
              $ Type.Application
                  { ann
                  , function: Type.Unsolved a1
                  , argument: Type.Unsolved a2
                  }
          ]

      _context .= contexts.before <> between <> contexts.after
      solve a1 function

      contextN <- use _context
      solve a2 (Context.apply contextN argument)

    Type.KindApplication { ann, function, argument } -> do
      u1 <- fresh
      u2 <- fresh

      let
        a1 = { ann: FromDerived $ view Type._ann function, name: u1 }
        a2 = { ann: FromDerived $ view Type._ann argument, name: u2 }
        between = Context.fromArray
          [ Context.Unsolved u2 Nothing
          , Context.Unsolved u1 Nothing
          , Context.Solved a Nothing
              $ Type.Application
                  { ann
                  , function: Type.Unsolved a1
                  , argument: Type.Unsolved a2
                  }
          ]

      _context .= contexts.before <> between <> contexts.after
      solve a1 function

      contextN <- use _context
      solve a2 (Context.apply contextN argument)

check
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Expr From
  -> Type From
  -> m Unit
check = case _, _ of

  Expr.Literal _ (Expr.Char _), Type.Constructor { name: "Char" } ->
    pure unit
  Expr.Literal _ (Expr.String _), Type.Constructor { name: "String" } ->
    pure unit
  Expr.Literal _ (Expr.Int _), Type.Constructor { name: "Int" } ->
    pure unit
  Expr.Literal _ (Expr.Float _), Type.Constructor { name: "Float" } ->
    pure unit

  Expr.Literal _ (Expr.Array _), _ ->
    throwError "check: unimplemented"
  Expr.Literal _ (Expr.Object _), _ ->
    throwError "check: unimplemented"

  Expr.Lambda _ argument expression, t
    | Just f <- preview Type._Function t ->
        withNameInEnvironment argument f.argument $ check expression f.result

  e, Type.Forall { ann, name, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    withTypeVariableInContext name' Nothing do
      check e $ Type.substituteType name (Type.Skolem { ann: FromDerived ann, name: name' }) type_

  e, t -> do
    t' <- infer e
    context <- use _context
    subsumes (Context.apply context t') (Context.apply context t)

infer
  :: forall m. MonadState (CheckState From) m => MonadError String m => Expr From -> m (Type From)
infer = case _ of

  Expr.Literal ann literal -> case literal of
    Expr.Char _ ->
      pure $ Type.Constructor { ann: FromDerived ann, name: "Char" }
    Expr.String _ ->
      pure $ Type.Constructor { ann: FromDerived ann, name: "String" }
    Expr.Int _ ->
      pure $ Type.Constructor { ann: FromDerived ann, name: "Int" }
    Expr.Float _ ->
      pure $ Type.Constructor { ann: FromDerived ann, name: "Float" }
    Expr.Array _ ->
      throwError "infer: unimplemented"
    Expr.Object _ ->
      throwError "infer: unimplemented"

  Expr.Variable _ name -> do
    mType <- use (_environment <<< _atNames name)
    case mType of
      Just type_ ->
        pure type_
      Nothing ->
        throwError "infer: variable not in environment"

  Expr.Lambda ann argument expression -> do
    u1 <- fresh
    u2 <- fresh

    _context %= flip append
      ( Context.fromArray
          [ Context.Unsolved u1 Nothing
          , Context.Unsolved u2 Nothing
          ]
      )

    let
      t1 = Type.Unsolved { ann: FromDerived ann, name: u1 }
      t2 = Type.Unsolved { ann: FromDerived ann, name: u2 }

    withNameInEnvironment argument t1 $ check expression t2

    pure $ review Type._Function
      { ann0: FromDerived ann
      , ann1: FromDerived ann
      , ann2: FromDerived ann
      , argument: t1
      , result: t2
      }

  Expr.Apply _ function argument -> do
    functionType <- infer function
    context <- use _context
    inferApplication (Context.apply context functionType) argument

  Expr.Annotate _ expression type_ ->
    check expression type_ $> type_

  Expr.Let ann key value expr -> do
    valueUnsolved <- fresh
    exprUnsolved <- fresh

    _context %= flip append
      ( Context.fromArray
          [ Context.Unsolved valueUnsolved Nothing
          , Context.Unsolved exprUnsolved Nothing
          ]
      )

    let
      valueType = Type.Unsolved { ann: FromDerived ann, name: valueUnsolved }
      exprType = Type.Unsolved { ann: FromDerived ann, name: exprUnsolved }

    withNameInEnvironment key valueType do
      check value valueType
      check expr exprType

    pure exprType

  Expr.IfThenElse ann if_ then_ else_ -> do
    u <- fresh

    let t = Type.Unsolved { ann: FromDerived ann, name: u }

    check if_ (Type.Constructor { ann: FromAbyss, name: "Boolean" })

    _context %= Context.push (Context.Unsolved u Nothing)

    check then_ t
    check else_ t

    pure t

inferApplication
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Type From
  -> Expr From
  -> m (Type From)
inferApplication = case _, _ of

  Type.Forall { ann, name, type_ }, e -> do
    name' <- fresh
    _context %= Context.push (Context.Unsolved name' Nothing)
    inferApplication
      (Type.substituteType name (Type.Unsolved { ann: FromDerived ann, name: name' }) type_)
      e

  Type.Unsolved { ann, name }, e -> do
    contexts <- splitContextAtUnsolved name

    u1 <- fresh
    u2 <- fresh

    let
      t1 = Type.Unsolved { ann: FromDerived ann, name: u1 }
      t2 = Type.Unsolved { ann: FromDerived ann, name: u2 }
      between = Context.fromArray
        [ Context.Unsolved u2 Nothing
        , Context.Unsolved u1 Nothing
        , Context.Solved name Nothing $
            review Type._Function
              { ann0: FromDerived ann
              , ann1: FromDerived ann
              , ann2: FromDerived ann
              , argument: t1
              , result: t2
              }
        ]

    _context .= contexts.before <> between <> contexts.after

    check e t1

    pure t2

  t, e
    | Just f <- preview Type._Function t ->
        check e f.argument $> f.result

  _, _ ->
    throwError "inferApplication: cannot apply"
