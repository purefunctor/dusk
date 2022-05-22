module Dusk.Ast.Traversals.Type
  ( treadTypeEndo
  , treadTypeEndoM
  ) where

import Prelude
import Prim hiding (Type)

import Control.Monad.Rec.Class (class MonadRec, Step(..), tailRecM)
import Data.Function.Uncurried (Fn2, Fn3, mkFn2, mkFn3, runFn2, runFn3)
import Data.Identity (Identity(..))
import Data.Newtype (unwrap)
import Data.Traversable (traverse)
import Dusk.Ast.Type (Type(..))
import Safe.Coerce (coerce)
import Uncurried.StateC (StateC(..))

--

newtype TypeYieldEndo r a = TypeYieldEndo
  { onEnter :: Fn3 (TypeYieldEndo r a) (Type a) (Fn2 (TypeYieldEndo r a) (Type a) r) r
  , onLeave :: Fn3 (TypeYieldEndo r a) (Type a) (Fn2 (TypeYieldEndo r a) (Type a) r) r
  }

--

typeTreadingEndo :: forall r a. Type a -> StateC r (TypeYieldEndo r a) (Type a)
typeTreadingEndo =
  let
    goType = mkFn3 \state1@(TypeYieldEndo yield1) type1 done ->
      runFn3 yield1.onEnter state1 type1
        ( mkFn2 \state2@(TypeYieldEndo yield2) -> case _ of
            Forall { ann, name, kind_, type_ } ->
              let
                kindTraversal = unwrap $ traverse typeTreadingEndo kind_
              in
                runFn2 kindTraversal state2
                  ( mkFn2 \state3 kind_' ->
                      runFn3 goType state3 type_
                        ( mkFn2 \state4@(TypeYieldEndo yield4) type_' ->
                            let
                              t' = Forall
                                { ann
                                , name
                                , kind_: kind_'
                                , type_: type_'
                                }
                            in
                              runFn3 yield4.onLeave state4 t' done
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
                            runFn3 yield4.onLeave state4 t' done
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
                            runFn3 yield4.onLeave state4 t' done
                      )
                )

            original@(Variable _) ->
              runFn3 yield2.onLeave state2 original done

            original@(Skolem _) ->
              runFn3 yield2.onLeave state2 original done

            original@(Unsolved _) ->
              runFn3 yield2.onLeave state2 original done

            original@(Constructor _) ->
              runFn3 yield2.onLeave state2 original done
        )
  in
    \type0 -> StateC $ mkFn2 \state0 done ->
      runFn3 goType state0 type0 done

--

treadTypeEndoM
  :: forall m a
   . MonadRec m
  => { onEnter :: Type a -> m (Type a)
     , onLeave :: Type a -> m (Type a)
     }
  -> Type a
  -> m (Type a)
treadTypeEndoM { onEnter, onLeave } type0 =
  let
    go = tailRecM case _ of
      RunTypeTreadingEndoMore s mt k -> do
        t <- mt
        pure $ Loop $ runFn2 k s t
      RunTypeTreadingEndoStop t ->
        pure $ Done t

    treading = unwrap $ typeTreadingEndo type0

    yield = TypeYieldEndo
      { onEnter: mkFn3 \s t k ->
          RunTypeTreadingEndoMore s (onEnter t) k
      , onLeave: mkFn3 \s t k ->
          RunTypeTreadingEndoMore s (onLeave t) k
      }
  in
    go $ runFn2 treading yield $ mkFn2 \_ a -> RunTypeTreadingEndoStop a

treadTypeEndo
  :: forall a
   . { onEnter :: Type a -> Type a
     , onLeave :: Type a -> Type a
     }
  -> Type a
  -> Type a
treadTypeEndo f t =
  case treadTypeEndoM (coerce f) t of
    Identity result -> result

--

data RunTypeTreadingEndo m a
  = RunTypeTreadingEndoMore
      -- State
      (TypeYieldEndo (RunTypeTreadingEndo m a) a)
      -- Value
      (m (Type a))
      -- Continuation
      (Fn2 (TypeYieldEndo (RunTypeTreadingEndo m a) a) (Type a) (RunTypeTreadingEndo m a))
  | RunTypeTreadingEndoStop
      -- Result
      (Type a)
