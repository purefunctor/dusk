-- | This modules defines the `Type` type and its associated traversals.
module Dusk.Ast.Types.Type
  ( Type(..)
  , TypeContext(..)
  , traverseTypeEndo
  , traverseTypeEndoM
  , traverseTypeEndoCtx
  , traverseTypeEndoCtxM
  ) where

import Prelude
import Prim hiding (Type)

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Function.Uncurried (Fn2, Fn3, mkFn2, mkFn3, runFn2, runFn3)
import Data.Identity (Identity(..))
import Data.List (List(..), (:))
import Data.Maybe (Maybe)
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Safe.Coerce (coerce)
import Uncurried.StateC (StateC(..))

--

data Type a
  = Forall { ann :: a, name :: String, kind_ :: Maybe (Type a), type_ :: Type a }
  | Variable { ann :: a, name :: String }
  | Skolem { ann :: a, name :: String }
  | Unsolved { ann :: a, name :: Int }
  | Constructor { ann :: a, name :: String }
  | Application { ann :: a, function :: Type a, argument :: Type a }
  | KindApplication { ann :: a, function :: Type a, argument :: Type a }

instance Eq (Type a) where
  eq = case _, _ of
    Forall f1, Forall f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Skolem f1, Skolem f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Unsolved f1, Unsolved f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Constructor f1, Constructor f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Application f1, Application f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    KindApplication f1, KindApplication f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    _, _ ->
      false

instance Ord (Type a) where
  compare = case _, _ of
    Forall f1, Forall f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Skolem f1, Skolem f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Unsolved f1, Unsolved f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Constructor f1, Constructor f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Application f1, Application f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    KindApplication f1, KindApplication f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    t1, t2 ->
      typeIndex t1 `compare` typeIndex t2
    where
    typeIndex = case _ of
      Forall _ -> 0
      Variable _ -> 1
      Skolem _ -> 2
      Unsolved _ -> 3
      Constructor _ -> 4
      Application _ -> 5
      KindApplication _ -> 6

derive instance Functor Type

--

data TypeContext = InForallKind | InForallType | InAbyss

derive instance Eq TypeContext

newtype TypeYieldEndo r a = TypeYieldEndo
  { context :: List TypeContext
  , onEnter :: Fn3 (TypeYieldEndo r a) (Type a) (Fn2 (TypeYieldEndo r a) (Type a) r) r
  , onLeave :: Fn3 (TypeYieldEndo r a) (Type a) (Fn2 (TypeYieldEndo r a) (Type a) r) r
  }

pushContext :: forall r a. TypeYieldEndo r a -> TypeContext -> TypeYieldEndo r a
pushContext (TypeYieldEndo fields) context = TypeYieldEndo $ fields
  { context = context : fields.context }

discardContext :: forall r a. TypeYieldEndo r a -> TypeYieldEndo r a
discardContext (TypeYieldEndo fields) =
  case fields.context of
    Nil ->
      TypeYieldEndo $ fields { context = fields.context }
    _ : tail ->
      TypeYieldEndo $ fields { context = tail }

--

typeTraversalEndo :: forall r a. Type a -> StateC r (TypeYieldEndo r a) (Type a)
typeTraversalEndo =
  let
    goType = mkFn3 \state1@(TypeYieldEndo yield1) type1 done ->
      runFn3 yield1.onEnter state1 type1
        ( mkFn2 \state2@(TypeYieldEndo yield2) -> case _ of
            Forall { ann, name, kind_, type_ } ->
              let
                kindTraversal = unwrap $ traverse typeTraversalEndo kind_
              in
                runFn2 kindTraversal (pushContext state2 InForallKind)
                  ( mkFn2 \state3 kind_' ->
                      runFn3 goType (pushContext state3 InForallType) type_
                        ( mkFn2 \state4@(TypeYieldEndo yield4) type_' ->
                            let
                              t' = Forall
                                { ann
                                , name
                                , kind_: kind_'
                                , type_: type_'
                                }
                            in
                              runFn3 yield4.onLeave (discardContext state4) t' done
                        )
                  )

            Application { ann, function, argument } ->
              runFn3 goType state2 function
                ( mkFn2 \state3 function' ->
                    runFn3 goType state3 argument
                      ( mkFn2 \state4@(TypeYieldEndo yield4) argument' ->
                          let
                            t' = Application
                              { ann
                              , function: function'
                              , argument: argument'
                              }
                          in
                            runFn3 yield4.onLeave (discardContext state4) t' done
                      )
                )

            KindApplication { ann, function, argument } ->
              runFn3 goType state2 function
                ( mkFn2 \state3 function' ->
                    runFn3 goType state3 argument
                      ( mkFn2 \state4@(TypeYieldEndo yield4) argument' ->
                          let
                            t' = KindApplication
                              { ann
                              , function: function'
                              , argument: argument'
                              }
                          in
                            runFn3 yield4.onLeave (discardContext state4) t' done
                      )
                )

            original@(Variable _) ->
              runFn3 yield2.onLeave (discardContext state2) original done

            original@(Skolem _) ->
              runFn3 yield2.onLeave (discardContext state2) original done

            original@(Unsolved _) ->
              runFn3 yield2.onLeave (discardContext state2) original done

            original@(Constructor _) ->
              runFn3 yield2.onLeave (discardContext state2) original done
        )
  in
    \type0 -> StateC $ mkFn2 \state0 done ->
      runFn3 goType state0 type0 done

--

traverseTypeEndoCtxM
  :: forall m a
   . MonadRec m
  => { onEnter :: TypeContext -> Type a -> m (Type a)
     , onLeave :: TypeContext -> Type a -> m (Type a)
     }
  -> Type a
  -> m (Type a)
traverseTypeEndoCtxM { onEnter, onLeave } type0 =
  let
    go = tailRecM case _ of
      RunTypeTraversalEndoMore s mt k -> do
        t <- mt
        pure $ Loop $ runFn2 k s t
      RunTypeTraversalEndoStop t ->
        pure $ Done t

    traverseing = unwrap $ typeTraversalEndo type0

    yield = TypeYieldEndo
      { context: Nil
      , onEnter: mkFn3 \s@(TypeYieldEndo { context }) t k ->
          let
            context' = case context of
              Nil -> InAbyss
              head : _ -> head
          in
            RunTypeTraversalEndoMore s (onEnter context' t) k
      , onLeave: mkFn3 \s@(TypeYieldEndo { context }) t k ->
          let
            context' = case context of
              Nil -> InAbyss
              head : _ -> head
          in
            RunTypeTraversalEndoMore s (onLeave context' t) k
      }
  in
    go $ runFn2 traverseing yield $ mkFn2 \_ a -> RunTypeTraversalEndoStop a

traverseTypeEndoM
  :: forall m a
   . MonadRec m
  => { onEnter :: Type a -> m (Type a)
     , onLeave :: Type a -> m (Type a)
     }
  -> Type a
  -> m (Type a)
traverseTypeEndoM { onEnter, onLeave } =
  traverseTypeEndoCtxM { onEnter: \_ -> onEnter, onLeave: \_ -> onLeave }

traverseTypeEndoCtx
  :: forall a
   . { onEnter :: TypeContext -> Type a -> Type a
     , onLeave :: TypeContext -> Type a -> Type a
     }
  -> Type a
  -> Type a
traverseTypeEndoCtx f t =
  case traverseTypeEndoCtxM (coerce f) t of
    Identity result -> result

traverseTypeEndo
  :: forall a
   . { onEnter :: Type a -> Type a
     , onLeave :: Type a -> Type a
     }
  -> Type a
  -> Type a
traverseTypeEndo f t =
  case traverseTypeEndoM (coerce f) t of
    Identity result -> result

--

data RunTypeTraversalEndo m a
  = RunTypeTraversalEndoMore
      -- State
      (TypeYieldEndo (RunTypeTraversalEndo m a) a)
      -- Value
      (m (Type a))
      -- Continuation
      (Fn2 (TypeYieldEndo (RunTypeTraversalEndo m a) a) (Type a) (RunTypeTraversalEndo m a))
  | RunTypeTraversalEndoStop
      -- Result
      (Type a)
