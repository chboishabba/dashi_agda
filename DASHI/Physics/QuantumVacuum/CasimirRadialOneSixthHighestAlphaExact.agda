module DASHI.Physics.QuantumVacuum.CasimirRadialOneSixthHighestAlphaExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealCubicMarxDerivativeExact as Cubic
import DASHI.Analysis.ConstructiveRealCubicCoefficientNormalisationExact as Cubic3
import DASHI.Physics.QuantumVacuum.CasimirOneSixthFactorisationExact as Sixth
import DASHI.Physics.QuantumVacuum.CasimirRadialMeasureOneSixthCutsetExact as Radial

------------------------------------------------------------------------
-- HIGHEST-ALPHA SPLIT OF THE TRANSVERSE 1/6 PAYMENT
--
-- OWNED:
--   D(u^3) = 3 u^2 at the repo's finite-difference derivative level;
--   2 * 3 = 6 arithmetic.
--
-- LIVE:
--   angular normalized measure supplies the inverse-2 factor;
--   field/primitive transport supplies inverse-3 on the same radial object;
--   improper/regulator endpoint theorem identifies the finite part.
------------------------------------------------------------------------

record RadialThirdPrimitiveCompletion : Set₁ where
  field
    ConstructedReal : Set
    RingNormalisation : Set
    FieldCapability : Set

    oneThird : Set
    threeTimesOneThirdIsOne : Set

    cubicDerivativeOwnerUsed : Set
    cubicDerivativeIsThreeTimesSquareUsed : Set
    scaledCubeDerivativeIsSquare : Set

    sameEnergyVariable : Set
    sameRadialIntegrandAfterSubstitution : Set
    improperEndpointOrRegulatorFinitePart : Set

    reading : String

open RadialThirdPrimitiveCompletion public

record AngularHalfCompletion : Set₁ where
  field
    polarMeasureTheorem : Radial.PolarMeasureTheorem
    angularIntegralIsTwoPiUsed : Set
    twoPiSquaredNormalizationUsed : Set
    inverseTwoCoefficientProduced : Set
    sameTransverseCasimirObject : Set
    reading : String

open AngularHalfCompletion public

record CasimirOneSixthHighestAlphaCompletion : Set₁ where
  field
    angular : AngularHalfCompletion
    radialThird : RadialThirdPrimitiveCompletion
    denominatorCompiler : 2 * 3 ≡ 6
    sameTransverseObject : Set
    oneSixthReceipt : Sixth.OneSixthAssembly
    reading : String

open CasimirOneSixthHighestAlphaCompletion public

canonicalDenominatorCompiler : 2 * 3 ≡ 6
canonicalDenominatorCompiler = refl

record OneSixthHighestAlphaStatus : Set where
  field
    cubicDerivativeFactorThreeOwned : Bool
    denominatorTwoTimesThreeOwned : Bool
    angularHalfClosed : Bool
    scaledCubePrimitiveClosed : Bool
    endpointFinitePartClosed : Bool

    cubicDerivativeFactorThreeOwnedIsTrue : cubicDerivativeFactorThreeOwned ≡ true
    denominatorTwoTimesThreeOwnedIsTrue : denominatorTwoTimesThreeOwned ≡ true
    angularHalfClosedIsFalse : angularHalfClosed ≡ false
    scaledCubePrimitiveClosedIsFalse : scaledCubePrimitiveClosed ≡ false
    endpointFinitePartClosedIsFalse : endpointFinitePartClosed ≡ false

open OneSixthHighestAlphaStatus public

canonicalOneSixthHighestAlphaStatus : OneSixthHighestAlphaStatus
canonicalOneSixthHighestAlphaStatus = record
  { cubicDerivativeFactorThreeOwned = true
  ; denominatorTwoTimesThreeOwned = true
  ; angularHalfClosed = false
  ; scaledCubePrimitiveClosed = false
  ; endpointFinitePartClosed = false
  ; cubicDerivativeFactorThreeOwnedIsTrue = refl
  ; denominatorTwoTimesThreeOwnedIsTrue = refl
  ; angularHalfClosedIsFalse = refl
  ; scaledCubePrimitiveClosedIsFalse = refl
  ; endpointFinitePartClosedIsFalse = refl
  }

data CubicDerivativeAutomaticallyProvesImproperIntegral : Set where

cubicDerivativeDoesNotAutoCloseImproperIntegral :
  CubicDerivativeAutomaticallyProvesImproperIntegral → ⊥
cubicDerivativeDoesNotAutoCloseImproperIntegral ()
