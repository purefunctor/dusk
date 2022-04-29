{ name = "my-project"
, dependencies =
  [ "aff"
  , "arrays"
  , "console"
  , "debug"
  , "dodo-printer"
  , "effect"
  , "either"
  , "foldable-traversable"
  , "lists"
  , "maybe"
  , "newtype"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "profunctor-lenses"
  , "spec"
  , "transformers"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
