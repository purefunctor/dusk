module Test.Main where

import Prelude

import Effect (Effect)
import Effect.Aff (launchAff_)
import Data.Lens (review)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Tuple.Nested ((/\))
import Dusk.Ast.Type (Type(..), _Function, substituteType')
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = launchAff_ $ runSpec [ consoleReporter ] do
  describe "Dusk.Ast.Type" do
    describe "substituteType" do
      it "removes any form of collisions" do
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
          actual = substituteType' replacements $ mkForall "a" $ mkFunction (mkVariable "a") (mkVariable "b")
          expected = mkForall "a4" $ mkFunction (mkVariable "a4") (mkVariable "a")

        (actual == expected) `shouldEqual` true
