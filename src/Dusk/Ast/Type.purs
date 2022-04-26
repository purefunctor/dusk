module Dusk.Ast.Type where

import Prelude hiding (apply)
import Prim hiding (Type)

import Data.Lens (Getter', to)
import Data.Lens.Prism (Prism', prism')
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Partial.Unsafe (unsafeCrashWith)

data Type a
  = Forall { ann :: a, name :: String, kind_ :: Maybe (Type a), type_ :: Type a }
  | Variable { ann :: a, name :: String }
  | Skolem { ann :: a, name :: String }
  | Unsolved { ann :: a, name :: Int }
  | Constructor { ann :: a, name :: String }
  | Application { ann :: a, function :: Type a, argument :: Type a }
  | KindApplication { ann :: a, function :: Type a, argument :: Type a }

derive instance Eq a => Eq (Type a)
derive instance Ord a => Ord (Type a)
derive instance Functor Type

solveType :: forall a. Int -> Type a -> Type a -> Type a
solveType _ (Forall _) _ = unsafeCrashWith "solveType: expected a monotype"
solveType u m t = case t of
  Forall fields@{ kind_, type_ } ->
    Forall $ fields
      { kind_ = solveType u m <$> kind_
      , type_ = solveType u m type_
      }
  Application fields@{ function, argument } ->
    Application $ fields
      { function = solveType u m function
      , argument = solveType u m argument
      }
  KindApplication fields@{ function, argument } ->
    KindApplication $ fields
      { function = solveType u m function
      , argument = solveType u m argument
      }
  Unsolved { name: u' } | u == u' -> m
  _ -> t

annForType :: forall a. Getter' (Type a) a
annForType = to case _ of
  Forall { ann } -> ann
  Variable { ann } -> ann
  Skolem { ann } -> ann
  Unsolved { ann } -> ann
  Constructor { ann } -> ann
  Application { ann } -> ann
  KindApplication { ann } -> ann

_Function
  :: forall a
   . Prism' (Type a)
       { ann0 :: a
       , ann1 :: a
       , ann2 :: a
       , argument :: Type a
       , result :: Type a
       }
_Function = prism' m u
  where
  m { ann0, ann1, ann2, argument, result } =
    Application
      { ann: ann0
      , function: Application
          { ann: ann1
          , function: Constructor
              { ann: ann2
              , name: "Function"
              }
          , argument: argument
          }
      , argument: result
      }

  u = case _ of
    Application
      { ann: ann0
      , function: Application
          { ann: ann1
          , function: Constructor
              { ann: ann2
              , name: "Function"
              }
          , argument: argument
          }
      , argument: result
      } ->
      Just { ann0, ann1, ann2, argument, result }
    _ ->
      Nothing
