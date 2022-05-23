-- | This module defines common operations for the `Type` node.
module Dusk.Ast.Type
  ( module Dusk.Ast.Type
  , module Dusk.Ast.Types.Type
  ) where

import Prelude hiding (apply)
import Prim hiding (Type)

import Control.Monad.Writer.Class (tell)
import Data.Foldable (foldMap)
import Data.Lens (Lens', lens)
import Data.Lens.Prism (Prism', prism')
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Debug as Debug
import Dusk.Ast.Types.Type (Type(..), traverseTypeEndo, traverseTypeEndoM)
import Partial.Unsafe (unsafeCrashWith)
import Uncurried.Writer (Writer, execWriter)

--------------------------------------------------------------------------------
------------------------------------- QUERIES ----------------------------------
--------------------------------------------------------------------------------

-- | Determines whether or not a type is a monotype.
isMonoType :: forall a. Type a -> Boolean
isMonoType = case _ of
  Forall _ ->
    false
  _ ->
    true

-- | Collects all type variables in a type, regardless if they're free
-- | or bound.
variablesInType :: forall a. Type a -> Set String
variablesInType = execWriter <<< traverseTypeEndoM { onEnter, onLeave: pure }
  where
  onEnter :: Type a -> Writer (Set String) (Type a)
  onEnter t = case t of
    Variable { name } ->
      tell (Set.singleton name) $> t
    _ ->
      pure t

--------------------------------------------------------------------------------
----------------------------------- TRAVERSALS ---------------------------------
--------------------------------------------------------------------------------

-- | Given an unsolved type variable `u`, a replacement type `r`, this
-- | substitutes all occurences of `u` with `r` on a type.
-- |
-- | Note: this function crashes when `r` is a polytype, as we currently
-- | restrict type impredicativity in the type system.
solveType :: forall a. Int -> Type a -> Type a -> Type a
solveType name into from =
  let
    onEnter :: Type a -> Type a
    onEnter = case _ of
      Unsolved { name: name' } | name == name' ->
        into
      original ->
        original
  in
    case into of
      Forall _ ->
        unsafeCrashWith "solveType: impredicativity!"
      _ ->
        traverseTypeEndo { onEnter, onLeave: identity } from

-- | Given a type variable `v`, a replacement type `r`, this substitutes
-- | all occurences of `v` with `r` on a type.
substituteType :: forall a. String -> Type a -> Type a -> Type a
substituteType k v = substituteType' (Map.singleton k v)

-- | Given a `Map` of type variables `v` to replacement types `r`, this
-- | substitutes all occurences of `v` with `r` on a type, while also
-- | making sure that names are never shadowed.
substituteType' :: forall a. Map String (Type a) -> Type a -> Type a
substituteType' = go Set.empty
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

substituteUnsolved' :: forall a. Map Int String -> Type a -> Type a
substituteUnsolved' known = traverseTypeEndo { onEnter, onLeave: identity }
  where
  onEnter :: Type a -> Type a
  onEnter = case _ of
    Unsolved { ann, name } | Just name' <- Map.lookup name known ->
      Variable { ann, name: name' }
    original ->
      original

--------------------------------------------------------------------------------
------------------------------------- OPTICS -----------------------------------
--------------------------------------------------------------------------------

-- | An optic that focuses on a `Type`'s annotation.
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

-- | A prism that constructs and deconstructs a `Function` type.
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
