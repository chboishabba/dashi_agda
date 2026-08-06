module DASHI.Physics.Foundations.Round5CompletionRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound5CompletionBoundary as Completion
import DASHI.Biology.ConsciousAccessRound5CompletionSourceAtlas as CompletionSources
import DASHI.Biology.ReducedFiftyThreeFibreExact as Reduced
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSPWeave
import DASHI.Physics.Foundations.PR399FoundationsCrossPollinationExact as Cross399
import DASHI.Physics.Foundations.Round5CombinedSourceBoundary as CombinedSources

completionBoundaryRegression :
  Completion.ConsciousAccessRound5CompletionBoundary
completionBoundaryRegression =
  Completion.canonicalConsciousAccessRound5CompletionBoundary

reducedFibreRegression :
  Reduced.fullSixByNineDimension ≡ 54
  ×
  Reduced.reducedDimension ≡ 53
reducedFibreRegression = refl , refl

moonshineDimensionRegression :
  Reduced.moonshineFirstPositiveCoefficientCandidate ≡ 196884
  ×
  Reduced.moonshineNontrivialDimensionCandidate ≡ 196883
moonshineDimensionRegression = refl , refl

oggProductRegression : 47 * 59 * 71 ≡ 196883
oggProductRegression = Cross399.largestThreeOggPrimeProductIs196883

sspPrimeAtlasRegression :
  SSPWeave.listCount SSPWeave.canonicalSSPPrimes ≡ 15
sspPrimeAtlasRegression = SSPWeave.canonicalSSPPrimeCountIsFifteen

geometricFiftyThreeNormalFormRegression :
  SSPWeave.presentationCost SSPWeave.canonicalFiftyThreePresentation
  ≤
  SSPWeave.presentationCost SSPWeave.virtualFiftyNineSevenUnit
geometricFiftyThreeNormalFormRegression =
  SSPWeave.canonicalPresentationIsCostMinimal
    SSPWeave.virtualFiftyNineSevenUnit

completionSourceAtlasRegression :
  CompletionSources.canonicalRound5CompletionSourceCount ≡ 31
completionSourceAtlasRegression =
  CompletionSources.canonicalRound5CompletionSourceCountIsThirtyOne

combinedSourceBoundaryRegression :
  CombinedSources.Round5CombinedSourceBoundary
combinedSourceBoundaryRegression =
  CombinedSources.canonicalRound5CombinedSourceBoundary
