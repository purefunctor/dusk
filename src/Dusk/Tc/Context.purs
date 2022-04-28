module Dusk.Tc.Context where

import Prelude
import Prim hiding (Type)

import Data.Array as Array
import Data.Foldable (fold, foldl)
import Data.List (List(..), (:))
import Data.List as List
import Data.Maybe (Maybe(..))
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

splitAtUnsolved :: forall a. Int -> Context a -> Maybe { before :: Context a, after :: Context a }
splitAtUnsolved unsolved (Context context) =
  let
    { init, rest } = List.span go context
  in
    case rest of
      Nil -> Nothing
      Cons _ rest -> Just
        { before: Context $ rest
        , after: Context $ init
        }
  where
  go (Unsolved unsolved' _) | unsolved == unsolved' = false
  go _ = true

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

lookupUnsolved :: forall a. Int -> Context a -> Maybe { name :: Int, kind_ :: Maybe (Type a) }
lookupUnsolved name (Context context) = List.findMap go context
  where
  go (Unsolved name' kind_) | name == name' = Just { name, kind_ }
  go _ = Nothing

