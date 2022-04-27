module Dusk.Tc.Context where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (fold, foldl)
import Data.List (List, (:))
import Data.List as List
import Data.Maybe (Maybe)
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

derive newtype instance Eq a => Eq (Context a)
derive newtype instance Ord a => Ord (Context a)
derive instance Functor Context

fromArray :: forall a. Array (Element a) -> Context a
fromArray = Context <<< List.fromFoldable <<< Array.reverse

push :: forall a. Element a -> Context a -> Context a
push element (Context context) = Context (element : context)

apply :: forall a. Context a -> Type a -> Type a
apply (Context context) = flip (foldl go) context
  where
  go t (Solved u _ m) = Type.solveType u m t
  go t _ = t

discardUntil :: forall a. Context a -> Element a -> Context a
discardUntil (Context context) element =
  Context $ fold $ List.tail $ _.rest $ List.span (_ /= element) context
