module Dusk.Ast.Expr where

import Prelude

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

derive instance Eq a => Eq (Expr a)
derive instance Ord a => Ord (Expr a)
derive instance Functor Expr
