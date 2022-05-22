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
  , "functions"
  , "identity"
  , "lists"
  , "maybe"
  , "newtype"
  , "ordered-collections"
  , "partial"
  , "prelude"
  , "profunctor-lenses"
  , "safe-coerce"
  , "spec"
  , "tailrec"
  , "transformers"
  , "tuples"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs", "test/**/*.purs" ]
}
