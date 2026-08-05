module DASHI.Biology.ConsciousAccessRound3CompleteRegression where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)

import DASHI.Biology.ConsciousAccessRound3ExtendedRegression as Regression
import DASHI.Biology.ConsciousAccessRound3SourceAtlas as CoreSources
import DASHI.Biology.ConsciousAccessRound3ExtendedSourceAtlas as ExtendedSources

record ConsciousAccessRound3CompleteRegression : Setω where
  field
    theoremSurface :
      Regression.ConsciousAccessRound3ExtendedRegression

    coreSourceCount :
      CoreSources.canonicalRound3SourceCount ≡ 9

    extendedSourceCount :
      ExtendedSources.canonicalRound3ExtendedSourceCount ≡ 4

open ConsciousAccessRound3CompleteRegression public

canonicalConsciousAccessRound3CompleteRegression :
  ConsciousAccessRound3CompleteRegression
canonicalConsciousAccessRound3CompleteRegression =
  record
    { theoremSurface =
        Regression.canonicalConsciousAccessRound3ExtendedRegression
    ; coreSourceCount =
        CoreSources.canonicalRound3SourceCountIsNine
    ; extendedSourceCount =
        ExtendedSources.canonicalRound3ExtendedSourceCountIsFour
    }
