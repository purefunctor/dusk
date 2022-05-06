module Dusk.Ast.Ann where

import Prelude

newtype SourcePos = SourcePos
  { line :: Int
  , column :: Int
  }

derive newtype instance Eq SourcePos
derive newtype instance Ord SourcePos

newtype SourceSpan = SourceSpan
  { start :: SourcePos
  , end :: SourcePos
  }

derive newtype instance Eq SourceSpan
derive newtype instance Ord SourceSpan

-- | The origin of a syntax node
-- |
-- | * abyss - defined in the compiler
-- | * source - defined in a source file
-- | * derived - defined from another node
data From
  = FromAbyss
  | FromSource SourceSpan
  | FromDerived From

derive instance Eq From
derive instance Ord From

unfixFrom :: From -> From
unfixFrom = case _ of
  FromDerived from -> unfixFrom from
  from -> from
