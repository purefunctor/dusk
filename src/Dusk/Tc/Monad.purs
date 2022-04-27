module Dusk.Tc.Monad where

import Prelude

import Control.Monad.State.Class (class MonadState, gets, modify_)
import Data.Maybe (Maybe(..))
import Dusk.Tc.Context (Context)
import Dusk.Tc.Context as Context

type CheckState a =
  { count :: Int
  , context :: Context a
  }

fresh :: forall a m. MonadState (CheckState a) m => m Int
fresh = gets _.count <* modify_ (\s -> s { count = s.count + 1 })

withTypeVariableInContext
  :: forall a m r. MonadState (CheckState a) m => String -> m r -> m r
withTypeVariableInContext name action = do
  let element = Context.Variable name Nothing
  modify_ $ \s -> s { context = Context.push element s.context }
  result <- action
  modify_ $ \s -> s { context = Context.discardUntil s.context element }
  pure result

withUnsolvedTypeInContext :: forall a m r. MonadState (CheckState a) m => Int -> m r -> m r
withUnsolvedTypeInContext name action = do
  let
    marker = Context.Marker (show name)
    element = Context.Unsolved name Nothing
  modify_ $ \s ->
    s
      { context = Context.push element $ Context.push marker s.context
      }
  result <- action
  modify_ $ \s ->
    s
      { context = Context.discardUntil s.context marker
      }
  pure result
