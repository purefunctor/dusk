module Dusk.Environment where

import Prelude
import Prim hiding (Type)

import Data.Lens (Lens', lens)
import Data.Lens.At (at)
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Dusk.Ast.Type (Type)

type Environment a =
  { names :: Map String (Type a)
  , types :: Map String (Type a)
  }

_names :: forall a. Lens' (Environment a) (Map String (Type a))
_names = lens _.names (_ { names = _ })

_types :: forall a. Lens' (Environment a) (Map String (Type a))
_types = lens _.types (_ { types = _ })

_atNames :: forall a. String -> Lens' (Environment a) (Maybe (Type a))
_atNames name = _names <<< at name

_atTypes :: forall a. String -> Lens' (Environment a) (Maybe (Type a))
_atTypes type_ = _types <<< at type_

emptyEnvironment :: forall a. Environment a
emptyEnvironment = { names: Map.empty, types: Map.empty }
