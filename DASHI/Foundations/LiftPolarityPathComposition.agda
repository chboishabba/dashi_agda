module DASHI.Foundations.LiftPolarityPathComposition where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Foundations.RecursiveRadixHypervoxel as Hyper

open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  )

------------------------------------------------------------------------
-- A path carries one central-lift transition per scale or transport step.
------------------------------------------------------------------------

Polarity : Set
Polarity = OrientationPolarity

PolarityPath : Set
PolarityPath = List Polarity

infixr 5 _++p_
_++p_ : PolarityPath → PolarityPath → PolarityPath
[] ++p ys = ys
(x ∷ xs) ++p ys = x ∷ (xs ++p ys)

composePolarityPath : PolarityPath → Polarity
composePolarityPath [] = positive
composePolarityPath (x ∷ xs) =
  Hyper.multiplyPolarity x (composePolarityPath xs)

emptyPathHasPositiveLift : composePolarityPath [] ≡ positive
emptyPathHasPositiveLift = refl

singletonPathHasItsLift :
  ∀ polarity → composePolarityPath (polarity ∷ []) ≡ polarity
singletonPathHasItsLift positive = refl
singletonPathHasItsLift negative = refl

------------------------------------------------------------------------
-- Prefix/suffix factorisation: total lift = coarse lift * relative fine lift.
------------------------------------------------------------------------

composePolarityAppend :
  ∀ prefix suffix →
  composePolarityPath (prefix ++p suffix)
  ≡ Hyper.multiplyPolarity
      (composePolarityPath prefix)
      (composePolarityPath suffix)
composePolarityAppend [] suffix = refl
composePolarityAppend (x ∷ prefix) suffix =
  trans
    (cong (Hyper.multiplyPolarity x)
      (composePolarityAppend prefix suffix))
    (Hyper.polarityAssociative
      x
      (composePolarityPath prefix)
      (composePolarityPath suffix))

record CoarseFinePolarityFactorisation : Set where
  constructor coarse-fine-polarity-factorisation
  field
    coarsePrefix : PolarityPath
    relativeFineSuffix : PolarityPath
    totalPath : PolarityPath
    totalPathIsJoin : totalPath ≡ coarsePrefix ++p relativeFineSuffix
    totalLift : Polarity
    coarseLift : Polarity
    relativeFineLift : Polarity
    totalLiftIsComposedPath : totalLift ≡ composePolarityPath totalPath
    coarseLiftIsPrefixProduct : coarseLift ≡ composePolarityPath coarsePrefix
    relativeFineLiftIsSuffixProduct :
      relativeFineLift ≡ composePolarityPath relativeFineSuffix
    liftFactorisation :
      totalLift
      ≡ Hyper.multiplyPolarity coarseLift relativeFineLift

factorPolarityPath :
  (prefix suffix : PolarityPath) →
  CoarseFinePolarityFactorisation
factorPolarityPath prefix suffix =
  coarse-fine-polarity-factorisation
    prefix
    suffix
    (prefix ++p suffix)
    refl
    (composePolarityPath (prefix ++p suffix))
    (composePolarityPath prefix)
    (composePolarityPath suffix)
    refl
    refl
    refl
    (composePolarityAppend prefix suffix)

------------------------------------------------------------------------
-- Canonical examples.
------------------------------------------------------------------------

positiveNegativePath : PolarityPath
positiveNegativePath = positive ∷ negative ∷ []

negativeNegativePath : PolarityPath
negativeNegativePath = negative ∷ negative ∷ []

positiveNegativePathIsNegative :
  composePolarityPath positiveNegativePath ≡ negative
positiveNegativePathIsNegative = refl

negativeNegativePathIsPositive :
  composePolarityPath negativeNegativePath ≡ positive
negativeNegativePathIsPositive = refl

canonicalCoarseFineFactorisation : CoarseFinePolarityFactorisation
canonicalCoarseFineFactorisation =
  factorPolarityPath
    (negative ∷ [])
    (negative ∷ positive ∷ [])

------------------------------------------------------------------------
-- Boundary receipt.
------------------------------------------------------------------------

record PolarityPathAuthorityBoundary : Set where
  field
    polarityIsSpatialCoordinateClaimed : Bool
    projectedBaseDetectsEveryLiftClaimed : Bool
    pathProductIsExplicit : Bool
    prefixSuffixFactorisationIsProved : Bool
    spinorialSensitivityRequiresSeparateConsumer : Bool

canonicalPolarityPathAuthorityBoundary : PolarityPathAuthorityBoundary
canonicalPolarityPathAuthorityBoundary = record
  { polarityIsSpatialCoordinateClaimed = false
  ; projectedBaseDetectsEveryLiftClaimed = false
  ; pathProductIsExplicit = true
  ; prefixSuffixFactorisationIsProved = true
  ; spinorialSensitivityRequiresSeparateConsumer = true
  }

polarityPathSummary : String
polarityPathSummary =
  "Lift transitions compose by the two-element group law; a coarse prefix and relative fine suffix factor the total lift exactly."
