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
  = Literal { ann :: a, literal :: Literal (Expr a) }
  | Variable { ann :: a, name :: Prim.String }
  | Lambda { ann :: a, argument :: Prim.String, expression :: Expr a }
  | Apply { ann :: a, function :: Expr a, argument :: Expr a }
  | Annotate { ann :: a, expression :: Expr a, type_ :: Type a }
  | Let { ann :: a, name :: Prim.String, value :: Expr a, expression :: Expr a }
  | IfThenElse { ann :: a, if_ :: Expr a, then_ :: Expr a, else_ :: Expr a }

instance Eq (Expr a) where
  eq = case _, _ of
    Literal f1, Literal f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Lambda f1, Lambda f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Apply f1, Apply f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Annotate f1, Annotate f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Let f1, Let f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    IfThenElse f1, IfThenElse f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    _, _ ->
      false

instance Ord (Expr a) where
  compare = case _, _ of
    Literal f1, Literal f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Lambda f1, Lambda f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Apply f1, Apply f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Annotate f1, Annotate f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Let f1, Let f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    IfThenElse f1, IfThenElse f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    a, b ->
      exprIndex a `compare` exprIndex b
    where
    exprIndex = case _ of
      Literal _ -> 0
      Variable _ -> 1
      Lambda _ -> 2
      Apply _ -> 3
      Annotate _ -> 4
      Let _ -> 5
      IfThenElse _ -> 6

derive instance Functor Expr

_ann :: forall a. Lens' (Expr a) a
_ann = lens u m
  where
  u = case _ of
    Literal { ann } -> ann
    Variable { ann } -> ann
    Lambda { ann } -> ann
    Apply { ann } -> ann
    Annotate { ann } -> ann
    Let { ann } -> ann
    IfThenElse { ann } -> ann
  m expr ann = case expr of
    Literal f1 -> Literal $ f1 { ann = ann }
    Variable f1 -> Variable $ f1 { ann = ann }
    Lambda f1 -> Lambda $ f1 { ann = ann }
    Apply f1 -> Apply $ f1 { ann = ann }
    Annotate f1 -> Annotate $ f1 { ann = ann }
    Let f1 -> Let $ f1 { ann = ann }
    IfThenElse f1 -> IfThenElse $ f1 { ann = ann }
