module Dusk.Ast.Expr where

import Prelude

import Data.Lens (Lens', lens)
import Data.List (List)
import Data.Map (Map)
import Dusk.Ast.Type (Type)
import Prim as Prim

data Literal a
  = Char Prim.Char
  | String Prim.String
  | Int Prim.Int
  | Float Prim.Number
  | Array (List a)
  | Object (Map Prim.String a)

derive instance Eq a => Eq (Literal a)
derive instance Ord a => Ord (Literal a)
derive instance Functor Literal

data Expr a
  = Literal a (Literal (Expr a))
  | Variable a Prim.String
  | Lambda a Prim.String (Expr a)
  | Apply a (Expr a) (Expr a)
  | Annotate a (Expr a) (Type a)
  | Let a Prim.String (Expr a) (Expr a)
  | IfThenElse a (Expr a) (Expr a) (Expr a)

instance Eq (Expr a) where
  eq = case _, _ of
    Literal _ a, Literal _ b ->
      a == b
    Variable _ a, Variable _ b ->
      a == b
    Lambda _ a b, Lambda _ c d ->
      a == c && b == d
    Apply _ a b, Apply _ c d ->
      a == c && b == d
    Annotate _ a b, Annotate _ c d ->
      a == c && b == d
    Let _ a b c, Let _ d e f ->
      a == d && b == e && c == f
    IfThenElse _ a b c, IfThenElse _ d e f ->
      a == d && b == e && c == f
    _, _ ->
      false

instance Ord (Expr a) where
  compare = case _, _ of
    Literal _ a, Literal _ b ->
      a `compare` b
    Variable _ a, Variable _ b ->
      a `compare` b
    Lambda _ a b, Lambda _ c d ->
      a `compare` c <> b `compare` d
    Apply _ a b, Apply _ c d ->
      a `compare` c <> b `compare` d
    Annotate _ a b, Annotate _ c d ->
      a `compare` c <> b `compare` d
    IfThenElse _ a b c, IfThenElse _ d e f ->
      a `compare` d <> b `compare` e <> c `compare` f
    IfThenElse _ a b c, IfThenElse _ d e f ->
      a `compare` d <> b `compare` e <> c `compare` f
    a, b ->
      exprIndex a `compare` exprIndex b
    where
    exprIndex = case _ of
      Literal _ _ -> 0
      Variable _ _ -> 1
      Lambda _ _ _ -> 2
      Apply _ _ _ -> 3
      Annotate _ _ _ -> 4
      Let _ _ _ _ -> 5
      IfThenElse _ _ _ _ -> 6

derive instance Functor Expr

_ann :: forall a. Lens' (Expr a) a
_ann = lens u m
  where
  u = case _ of
    Literal a _ -> a
    Variable a _ -> a
    Lambda a _ _ -> a
    Apply a _ _ -> a
    Annotate a _ _ -> a
    Let a _ _ _ -> a
    IfThenElse a _ _ _ -> a
  m expr ann = case expr of
    Literal _ a -> Literal ann a
    Variable _ a -> Variable ann a
    Lambda _ a b -> Lambda ann a b
    Apply _ a b -> Apply ann a b
    Annotate _ a b -> Annotate ann a b
    Let _ a b c -> Let ann a b c
    IfThenElse _ a b c -> IfThenElse ann a b c
