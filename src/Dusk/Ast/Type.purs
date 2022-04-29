module Dusk.Ast.Type where

import Prelude hiding (apply)
import Prim hiding (Type)

import Data.Foldable (foldMap)
import Data.Lens (Lens', lens)
import Data.Lens.Prism (Prism', prism')
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Partial.Unsafe (unsafeCrashWith)

data Type a
  = Forall { ann :: a, name :: String, kind_ :: Maybe (Type a), type_ :: Type a }
  | Variable { ann :: a, name :: String }
  | Skolem { ann :: a, name :: String }
  | Unsolved { ann :: a, name :: Int }
  | Constructor { ann :: a, name :: String }
  | Application { ann :: a, function :: Type a, argument :: Type a }
  | KindApplication { ann :: a, function :: Type a, argument :: Type a }

instance Eq (Type a) where
  eq = case _, _ of
    Forall f1, Forall f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Skolem f1, Skolem f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Unsolved f1, Unsolved f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Constructor f1, Constructor f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    Application f1, Application f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    KindApplication f1, KindApplication f2 ->
      f1 { ann = unit } == f2 { ann = unit }
    _, _ ->
      false

instance Ord (Type a) where
  compare = case _, _ of
    Forall f1, Forall f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Variable f1, Variable f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Skolem f1, Skolem f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Unsolved f1, Unsolved f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Constructor f1, Constructor f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    Application f1, Application f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    KindApplication f1, KindApplication f2 ->
      f1 { ann = unit } `compare` f2 { ann = unit }
    t1, t2 ->
      typeIndex t1 `compare` typeIndex t2
    where
    typeIndex = case _ of
      Forall _ -> 0
      Variable _ -> 1
      Skolem _ -> 2
      Unsolved _ -> 3
      Constructor _ -> 4
      Application _ -> 5
      KindApplication _ -> 6

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

variablesInType :: forall a. Type a -> Set String
variablesInType = case _ of
  Forall { type_, kind_ } ->
    variablesInType type_ <> Set.unions (variablesInType <$> kind_)
  Variable { name } ->
    Set.singleton name
  Skolem _ ->
    Set.empty
  Unsolved _ ->
    Set.empty
  Constructor _ ->
    Set.empty
  Application { function, argument } ->
    variablesInType function <> variablesInType argument
  KindApplication { function, argument } ->
    variablesInType function <> variablesInType argument

substituteType :: forall a. String -> Type a -> Type a -> Type a
substituteType k v = substituteTypes (Map.singleton k v)

substituteTypes :: forall a. Map String (Type a) -> Type a -> Type a
substituteTypes = go Set.empty
  where
  freshen :: Set String -> String -> String
  freshen known = goFreshen 0
    where
    goFreshen :: Int -> String -> String
    goFreshen modifier current =
      let
        current' = current <> show modifier
      in
        if current' `Set.member` known then
          goFreshen (modifier + 1) current
        else
          current'

  go :: Set String -> Map String (Type a) -> Type a -> Type a
  go seen repl = case _ of
    Forall fields@{ ann, name, kind_, type_ }
      -- `Forall`-bound names cannot be replaced.
      | Map.member name repl ->
          Forall $ fields
            { kind_ = go seen repl <$> kind_
            }
      -- `Forall`-bound names that also appear in the replacements mapping must
      -- be renamed, as they potentially collide. Similarly, we also take into
      -- account the variables that we've already seen from other `Forall`s, as
      -- well as other keys that appear in the replacements mapping.
      --
      -- For example, given the following type:
      --
      -- forall a0 a. a -> b
      --
      -- and the following replacements mapping:
      --
      -- b  ~ a
      -- a1 ~ a2
      -- a2 ~ a3
      --
      -- We end up freshening the `Forall`-bound `a` into `a4` in the following
      -- type because of a few factors:
      --
      -- forall a0 a4. a4 -> a
      --
      -- * `a` appears in the replacement mapping in a value
      -- * `a0` is already bound by another `Forall`
      -- * `a1` appears in the replacement mapping in a key
      -- * `a2` appears in the replacement mapping as a key and value
      -- * `a3` appears in the replacement mapping in a value
      | varsInWith <- foldMap variablesInType repl
      , Set.member name varsInWith ->
          let
            name' = freshen (varsInWith <> seen <> Map.keys repl) name
            type_' = go seen (Map.singleton name (Variable { ann, name: name' })) type_
          in
            Forall $ fields
              { name = name'
              , kind_ = go seen repl <$> kind_
              , type_ = go (Set.insert name' seen) repl type_'
              }
      -- Otherwise...
      | otherwise ->
          Forall $ fields
            { kind_ = go seen repl <$> kind_
            , type_ = go (Set.insert name seen) repl type_
            }

    original@(Variable { name }) ->
      fromMaybe original (Map.lookup name repl)

    original@(Skolem _) -> original
    original@(Unsolved _) -> original
    original@(Constructor _) -> original

    Application fields@{ function, argument } ->
      Application $ fields
        { function = go seen repl function
        , argument = go seen repl argument
        }

    KindApplication fields@{ function, argument } ->
      KindApplication $ fields
        { function = go seen repl function
        , argument = go seen repl argument
        }

_ann :: forall a. Lens' (Type a) a
_ann = lens u m
  where
  u = case _ of
    Forall { ann } -> ann
    Variable { ann } -> ann
    Skolem { ann } -> ann
    Unsolved { ann } -> ann
    Constructor { ann } -> ann
    Application { ann } -> ann
    KindApplication { ann } -> ann

  m type_ ann = case type_ of
    Forall f -> Forall $ f { ann = ann }
    Variable f -> Variable $ f { ann = ann }
    Skolem f -> Skolem $ f { ann = ann }
    Unsolved f -> Unsolved $ f { ann = ann }
    Constructor f -> Constructor $ f { ann = ann }
    Application f -> Application $ f { ann = ann }
    KindApplication f -> KindApplication $ f { ann = ann }

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
