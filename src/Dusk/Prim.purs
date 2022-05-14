module Dusk.Prim where

import Prim hiding (Type)

import Data.Maybe (Maybe(..))
import Dusk.Ast.Ann (From(..))
import Dusk.Ast.Type (Type(..))

tyType :: Type From
tyType = Constructor
  { ann: FromAbyss
  , name: "Type"
  }

tyChar :: Type From
tyChar = Constructor
  { ann: FromAbyss
  , name: "Char"
  }

tyString :: Type From
tyString = Constructor
  { ann: FromAbyss
  , name: "String"
  }

tyInt :: Type From
tyInt = Constructor
  { ann: FromAbyss
  , name: "Int"
  }

tyFloat :: Type From
tyFloat = Constructor
  { ann: FromAbyss
  , name: "Float"
  }

tyBoolean :: Type From
tyBoolean = Constructor
  { ann: FromAbyss
  , name: "Boolean"
  }

jTyType :: Maybe (Type From)
jTyType = Just tyType
