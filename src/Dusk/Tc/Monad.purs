module Dusk.Tc.Monad where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Control.Monad.State.Class (class MonadState)
import Data.Lens (Lens', lens, use, (%=), (+=), (.=))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type
import Dusk.Environment (Environment, _names, emptyEnvironment)
import Dusk.Tc.Context (Context, Element, UnsolvedSplit)
import Dusk.Tc.Context as Context

type CheckState a =
  { count :: Int
  , context :: Context a
  , environment :: Environment a
  }

_count :: forall a. Lens' (CheckState a) Int
_count = lens _.count (_ { count = _ })

_context :: forall a. Lens' (CheckState a) (Context a)
_context = lens _.context (_ { context = _ })

_environment :: forall a. Lens' (CheckState a) (Environment a)
_environment = lens _.environment (_ { environment = _ })

emptyCheckState :: forall a. CheckState a
emptyCheckState =
  { count: 0
  , context: mempty
  , environment: emptyEnvironment
  }

fresh :: forall a m. MonadState (CheckState a) m => m Int
fresh = use _count <* (_count += 1)

type FreshUnsolved a =
  { fields :: { ann :: a, name :: Int }
  , type_ :: Type a
  , element :: Element a
  }

freshUnsolved
  :: forall a m. MonadState (CheckState a) m => a -> Maybe (Type a) -> m (FreshUnsolved a)
freshUnsolved a k = do
  u <- fresh
  let f = { ann: a, name: u }
  pure
    { fields: f
    , type_: Type.Unsolved f
    , element: Context.Unsolved u k
    }

splitContextAtUnsolved
  :: forall a m
   . MonadState (CheckState a) m
  => MonadError String m
  => Int
  -> m (UnsolvedSplit a)
splitContextAtUnsolved unsolved = do
  context <- use _context
  case Context.splitAtUnsolved unsolved context of
    Just fields -> pure fields
    Nothing -> throwError "cannot split context"

withNameInEnvironment
  :: forall a m r. MonadState (CheckState a) m => String -> Type a -> m r -> m r
withNameInEnvironment name type_ = withNamesInEnvironment (Map.singleton name type_)

withNamesInEnvironment
  :: forall a m r. MonadState (CheckState a) m => Map String (Type a) -> m r -> m r
withNamesInEnvironment names action = do
  original <- use _names'
  _names' %= Map.union names
  result <- action
  _names' .= original
  pure result
  where
  _names' :: Lens' (CheckState a) (Map String (Type a))
  _names' = _environment <<< _names

withTypeVariableInContext
  :: forall a m r. MonadState (CheckState a) m => String -> Maybe (Type a) -> m r -> m r
withTypeVariableInContext name kind_ action = do
  _context %= Context.push element
  result <- action
  _context %= Context.discardUntil element
  pure result
  where
  element = Context.Variable name kind_

withUnsolvedTypeInContext
  :: forall a m r. MonadState (CheckState a) m => Int -> Maybe (Type a) -> m r -> m r
withUnsolvedTypeInContext name kind_ action = do
  _context %= (Context.push element <<< Context.push marker)
  result <- action
  _context %= Context.discardUntil marker
  pure result
  where
  marker = Context.Marker (show name)
  element = Context.Unsolved name kind_
