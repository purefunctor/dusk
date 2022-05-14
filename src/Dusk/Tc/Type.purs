module Dusk.Tc.Type where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Lens (preview, review, set, use, view, (%=), (.=))
import Data.Maybe (Maybe(..), isNothing)
import Data.Traversable (traverse_)
import Dusk.Ast.Ann (From)
import Dusk.Ast.Expr (Expr)
import Dusk.Ast.Expr as Expr
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Environment (_atNames)
import Dusk.Prim as P
import Dusk.Tc.Context as Context
import Dusk.Tc.Monad
  ( CheckState
  , _context
  , _environment
  , fresh
  , freshUnsolved
  , splitContextAtUnsolved
  , withNameInEnvironment
  , withTypeVariableInContext
  , withUnsolvedTypeInContext
  )

type TypeExpr =
  { e :: Expr From
  , t :: Type From
  }

typeExprToExpr :: TypeExpr -> Expr From
typeExprToExpr { e, t } = Expr.Annotate
  { ann: view Expr._ann e
  , expression: e
  , type_: t
  }

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

  t1, Type.Forall { ann, name, kind_, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' kind_ $ subsumes t1 t2

  Type.Forall { ann, name, kind_, type_ }, t2 -> do
    name' <- fresh
    let t1 = Type.substituteType name (Type.Unsolved { ann, name: name' }) type_
    withUnsolvedTypeInContext name' kind_ $ subsumes t1 t2

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
      t1 = Type.substituteType f1.name (Type.Skolem { ann: f1.ann, name: name' })
        f1.type_
      t2 = Type.substituteType f2.name (Type.Skolem { ann: f2.ann, name: name' })
        f2.type_
    withTypeVariableInContext name' f1.kind_ $ unify t1 t2

  t1, Type.Forall { ann, name, kind_, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    let t2 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' kind_ $ unify t1 t2

  Type.Forall { ann, name, kind_, type_ }, t2 -> do
    name' <- append "t" <<< show <$> fresh
    let t1 = Type.substituteType name (Type.Skolem { ann, name: name' }) type_
    withTypeVariableInContext name' kind_ $ unify t1 t2

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
      _context .=
        Context.push (Context.Solved a P.jTyType m)
          contexts.before <> contexts.after

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
            context =
              Context.push (Context.Unsolved a P.jTyType)
                contexts.before
                <> contexts.after
            context' =
              Context.push
                ( Context.Solved b P.jTyType $
                    Type.Unsolved u
                )
                contexts'.before
                <> contexts'.after
          in
            _context .= context <> context'
        Nothing ->
          insertToContext t

    Type.Constructor _ ->
      insertToContext t

    _ | Just f <- preview Type._Function t -> do
      u1 <- freshUnsolved (view Type._ann f.argument) P.jTyType
      u2 <- freshUnsolved (view Type._ann f.result) P.jTyType

      let
        t' = review Type._Function $ f
          { argument = u1.type_
          , result = u2.type_
          }
        between = Context.fromArray
          [ u2.element
          , u1.element
          , Context.Solved a P.jTyType t'
          ]

      _context .= contexts.before <> between <> contexts.after
      solve u1.fields f.argument

      contextN <- use _context
      solve u2.fields (Context.apply contextN f.result)

    Type.Application { ann, function, argument } -> do
      u1 <- freshUnsolved (view Type._ann function) P.jTyType
      u2 <- freshUnsolved (view Type._ann argument) P.jTyType

      let
        t' = Type.Application
          { ann
          , function: u1.type_
          , argument: u2.type_
          }
        between = Context.fromArray
          [ u2.element
          , u1.element
          , Context.Solved a P.jTyType t'
          ]

      _context .= contexts.before <> between <> contexts.after
      solve u1.fields function

      contextN <- use _context
      solve u2.fields (Context.apply contextN argument)

    Type.KindApplication { ann, function, argument } -> do
      u1 <- freshUnsolved (view Type._ann function) P.jTyType
      u2 <- freshUnsolved (view Type._ann argument) P.jTyType

      let
        t' = Type.KindApplication
          { ann
          , function: u1.type_
          , argument: u2.type_
          }
        between = Context.fromArray
          [ u2.element
          , u1.element
          , Context.Solved a P.jTyType t'
          ]

      _context .= contexts.before <> between <> contexts.after
      solve u1.fields function

      contextN <- use _context
      solve u2.fields (Context.apply contextN argument)

check
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Expr From
  -> Type From
  -> m Unit
check = case _, _ of

  Expr.Literal { literal: Expr.Char _ }, Type.Constructor { name: "Char" } ->
    pure unit
  Expr.Literal { literal: Expr.String _ }, Type.Constructor { name: "String" } ->
    pure unit
  Expr.Literal { literal: Expr.Int _ }, Type.Constructor { name: "Int" } ->
    pure unit
  Expr.Literal { literal: Expr.Float _ }, Type.Constructor { name: "Float" } ->
    pure unit

  Expr.Literal { literal: Expr.Array _ }, _ ->
    throwError "check: unimplemented"
  Expr.Literal { literal: Expr.Object _ }, _ ->
    throwError "check: unimplemented"

  Expr.Lambda { argument, expression }, t
    | Just f <- preview Type._Function t ->
        withNameInEnvironment argument f.argument $ check expression f.result

  e, Type.Forall { ann, name, kind_, type_ } -> do
    name' <- append "t" <<< show <$> fresh
    withTypeVariableInContext name' kind_ do
      check e $ Type.substituteType name (Type.Skolem { ann, name: name' }) type_

  e, t -> do
    t' <- infer e
    context <- use _context
    subsumes (Context.apply context t') (Context.apply context t)

infer
  :: forall m. MonadState (CheckState From) m => MonadError String m => Expr From -> m (Type From)
infer = case _ of

  Expr.Literal { ann, literal } ->
    set Type._ann ann <$> case literal of
      Expr.Char _ ->
        pure P.tyChar
      Expr.String _ ->
        pure P.tyString
      Expr.Int _ ->
        pure P.tyInt
      Expr.Float _ ->
        pure P.tyFloat
      Expr.Array _ ->
        throwError "infer: unimplemented"
      Expr.Object _ ->
        throwError "infer: unimplemented"

  Expr.Variable { name } -> do
    mType <- use (_environment <<< _atNames name)
    case mType of
      Just type_ ->
        pure type_
      Nothing ->
        throwError "infer: variable not in environment"

  Expr.Lambda { ann, argument, expression } -> do
    u1 <- freshUnsolved ann P.jTyType
    u2 <- freshUnsolved ann P.jTyType

    _context %= flip append
      ( Context.fromArray
          [ u1.element
          , u2.element
          ]
      )

    withNameInEnvironment argument u1.type_ do
      check expression u2.type_

    pure $ review Type._Function
      { ann0: ann
      , ann1: ann
      , ann2: ann
      , argument: u1.type_
      , result: u2.type_
      }

  Expr.Apply { function, argument } -> do
    functionType <- infer function
    context <- use _context
    inferApplication (Context.apply context functionType) argument

  Expr.Annotate { expression, type_ } ->
    check expression type_ $> type_

  Expr.Let { ann, name, value, expression } -> do
    u <- freshUnsolved ann P.jTyType
    _context %= Context.push u.element

    expressionType <- withNameInEnvironment name u.type_ do
      check value u.type_
      infer expression

    context <- use _context
    pure $ Context.apply context expressionType

  Expr.IfThenElse { ann, if_, then_, else_ } -> do
    u <- freshUnsolved ann P.jTyType
    _context %= Context.push u.element

    check if_ P.tyBoolean
    check then_ u.type_
    check else_ u.type_

    pure u.type_

inferApplication
  :: forall m
   . MonadState (CheckState From) m
  => MonadError String m
  => Type From
  -> Expr From
  -> m (Type From)
inferApplication = case _, _ of

  Type.Forall { ann, name, kind_, type_ }, e -> do
    u <- freshUnsolved ann kind_
    _context %= Context.push u.element
    inferApplication (Type.substituteType name u.type_ type_) e

  Type.Unsolved { ann, name }, e -> do
    contexts <- splitContextAtUnsolved name

    u1 <- freshUnsolved ann P.jTyType
    u2 <- freshUnsolved ann P.jTyType

    let
      t' = review Type._Function
        { ann0: ann
        , ann1: ann
        , ann2: ann
        , argument: u1.type_
        , result: u2.type_
        }
      between = Context.fromArray
        [ u2.element
        , u1.element
        , Context.Solved name P.jTyType t'
        ]

    _context .= contexts.before <> between <> contexts.after

    check e u1.type_

    pure u2.type_

  t, e
    | Just f <- preview Type._Function t ->
        check e f.argument $> f.result

  _, _ ->
    throwError "inferApplication: cannot apply"
