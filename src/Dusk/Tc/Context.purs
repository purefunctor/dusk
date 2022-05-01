module Dusk.Tc.Context where

import Prelude
import Prim hiding (Type)

import Control.Monad.Error.Class (class MonadError, throwError)
import Data.Array as Array
import Data.Foldable (fold, foldl)
import Data.Lens (Getter', to)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..), isJust)
import Dusk.Ast.Type (Type)
import Dusk.Ast.Type as Type

data Element a
  = Variable String (Maybe (Type a))
  | Unsolved Int (Maybe (Type a))
  | Solved Int (Maybe (Type a)) (Type a)
  | Marker String

derive instance Eq (Element a)
derive instance Ord (Element a)
derive instance Functor Element

newtype Context a = Context (List (Element a))

derive newtype instance Eq (Context a)
derive newtype instance Ord (Context a)
derive instance Functor Context

instance Semigroup (Context a) where
  append (Context before) (Context after) = Context (after <> before)

instance Monoid (Context a) where
  mempty = Context Nil

fromArray :: forall a. Array (Element a) -> Context a
fromArray = Context <<< List.fromFoldable <<< Array.reverse

push :: forall a. Element a -> Context a -> Context a
push element (Context context) = Context (element : context)

discardUntil :: forall a. Element a -> Context a -> Context a
discardUntil element (Context context) =
  Context $ fold $ List.tail $ _.rest $ List.span (_ /= element) context

type UnsolvedSplit a =
  { before :: Context a
  , kind_ :: Maybe (Type a)
  , after :: Context a
  }

splitAtUnsolved :: forall a. Int -> Context a -> Maybe (UnsolvedSplit a)
splitAtUnsolved name (Context context) = go Nil context
  where
  go after = case _ of
    Nil ->
      Nothing
    Cons (Unsolved name' kind_) before
      | name == name' -> Just
          { before: Context $ before
          , kind_
          , after: Context $ List.reverse after
          }
    Cons current before ->
      go (current : after) before

type VariableSplit a =
  { before :: Context a
  , kind_ :: Maybe (Type a)
  , after :: Context a
  }

splitAtVariable :: forall a. String -> Context a -> Maybe (VariableSplit a)
splitAtVariable name (Context context) = go Nil context
  where
  go after = case _ of
    Nil ->
      Nothing
    Cons (Variable name' kind_) before
      | name == name' -> Just
          { before: Context $ before
          , kind_
          , after: Context $ List.reverse after
          }
    Cons current before ->
      go (current : after) before

apply :: forall a. Context a -> Type a -> Type a
apply (Context context) = flip (foldl go) context
  where
  go t (Solved u _ m) = Type.solveType u m t
  go t _ = t

lookupVariable :: forall a. String -> Context a -> Maybe { name :: String, kind_ :: Maybe (Type a) }
lookupVariable name (Context context) = List.findMap go context
  where
  go (Variable name' kind_) | name == name' = Just { name, kind_ }
  go _ = Nothing

gatherUnsolved :: forall a. Context a -> Context a
gatherUnsolved (Context context) = Context (List.filter go context)
  where
  go (Unsolved _ _) = true
  go _ = false

lookupUnsolved :: forall a. Int -> Context a -> Maybe { name :: Int, kind_ :: Maybe (Type a) }
lookupUnsolved name (Context context) = List.findMap go context
  where
  go (Unsolved name' kind_) | name == name' = Just { name, kind_ }
  go _ = Nothing

wellFormedType :: forall a m. MonadError String m => Context a -> Type a -> m Unit
wellFormedType = go
  where
  go context = case _ of
    Type.Forall { name, kind_, type_: type_' } ->
      go (push (Variable name kind_) context) type_'
    Type.Variable { name } ->
      if isJust $ lookupVariable name context then
        pure unit
      else
        throwError "syntactic variable not in scope"
    Type.Skolem { name } ->
      if isJust $ lookupVariable name context then
        pure unit
      else
        throwError "skolem variable not in scope"
    Type.Unsolved { name } ->
      if isJust $ lookupUnsolved name context then
        pure unit
      else
        throwError "unsolved variable not in scope"
    Type.Constructor _ ->
      pure unit
    Type.Application { function, argument } -> do
      go context function
      go context argument
    Type.KindApplication { function, argument } -> do
      go context function
      go context argument

_lookupVariable
  :: forall a. String -> Getter' (Context a) (Maybe { name :: String, kind_ :: Maybe (Type a) })
_lookupVariable = to <<< lookupVariable

_splitAtVariable
  :: forall a. String -> Getter' (Context a) (Maybe (VariableSplit a))
_splitAtVariable = to <<< splitAtVariable

_gatherUnsolved :: forall a. Getter' (Context a) (Context a)
_gatherUnsolved = to gatherUnsolved

_lookupUnsolved
  :: forall a. Int -> Getter' (Context a) (Maybe { name :: Int, kind_ :: Maybe (Type a) })
_lookupUnsolved = to <<< lookupUnsolved

_splitAtUnsolved :: forall a. Int -> Getter' (Context a) (Maybe (UnsolvedSplit a))
_splitAtUnsolved = to <<< splitAtUnsolved
