module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (Aff)
import Data.Lens (review)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Dusk.Ast.Type (Type(..), _Function, substituteTypes)
import Test.Unit (suite, test)
import Test.Unit.Main (runTest)
import Test.Unit.Assert as Assert

main :: Effect Unit
main = runTest do
  suite "Dusk.Ast.Type" do
    test "substituteType" substituteTypesUnit
  where
  substituteTypesUnit :: Aff Unit
  substituteTypesUnit =
    let
      mkFunction argument result = review _Function
        { ann0: unit
        , ann1: unit
        , ann2: unit
        , argument
        , result
        }
      mkVariable name = Variable
        { ann: unit
        , name
        }
      mkForall name type_ = Forall
        { ann: unit
        , name: "a0"
        , kind_: Nothing
        , type_: Forall
            { ann: unit
            , name
            , kind_: Nothing
            , type_
            }
        }
      replacements = Map.fromFoldable
        [ "b" /\ mkVariable "a"
        , "a1" /\ mkVariable "a2"
        , "a2" /\ mkVariable "a3"
        ]
      actual = substituteTypes replacements $ mkForall "a" $ mkFunction (mkVariable "a") (mkVariable "b")
      expected = mkForall "a4" $ mkFunction (mkVariable "a4") (mkVariable "a")
    in
      Assert.assert "a should be a4" $ actual == expected
