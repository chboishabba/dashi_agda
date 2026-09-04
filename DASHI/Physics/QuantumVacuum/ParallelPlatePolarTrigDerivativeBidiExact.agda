module DASHI.Physics.QuantumVacuum.ParallelPlatePolarTrigDerivativeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.PowerSeriesDifferentiationBidiCrossPollinationExact as PS
import DASHI.Analysis.BishopTrigonometricDerivedSeriesConvergenceExact as Derived
import DASHI.Physics.QuantumVacuum.ParallelPlatePolarJacobianBidiExact as Polar

------------------------------------------------------------------------
-- CASIMIR POLAR TRIG DERIVATIVE BIDI INSTANCE
--
-- The repo now owns a stronger downstream reduction: once finite differentiated
-- terms are pointwise identified with the existing Bishop cosine / minus-sine
-- terms, convergence of the derived series to those literal values is compiler
-- output.  It is therefore not an independent analytic leaf.
------------------------------------------------------------------------

record PolarTrigDerivativeProblems : Set₁ where
  field
    sineProblem cosineProblem : PS.PowerSeriesDerivativeProblem

    sineTargetIsCosine : Set
    cosineTargetIsNegativeSine : Set
    sameConstructedTrigCarrier : Set
    samePiAndAngleSemantics : Set
    reading : String

open PolarTrigDerivativeProblems public

record PolarTrigDerivativeCompletion
    (P : PolarTrigDerivativeProblems) : Set₁ where
  field
    sineDerivative : PS.PowerSeriesDerivativeReceipt (sineProblem P)
    cosineDerivative : PS.PowerSeriesDerivativeReceipt (cosineProblem P)

    sineDerivativeWeld : sineTargetIsCosine P
    cosineDerivativeWeld : cosineTargetIsNegativeSine P
    sameCarrierWeld : sameConstructedTrigCarrier P
    angleWeld : samePiAndAngleSemantics P

    polarDerivativeReceipt : Polar.ConstructedPolarDerivativeReceipt
    generatedFromTheseSeriesReceipts : Set

open PolarTrigDerivativeCompletion public

record ReversePolarTrigObligations : Set where
  field
    sineFiniteTermDerivativeIdentity : Set
    cosineFiniteTermDerivativeIdentity : Set
    derivativeLimitInterchange : Set
    sameConstructedSineCosine : Set

open ReversePolarTrigObligations public

data FormalSinCosSeriesAutomaticallyGiveCoordinateDerivatives : Set where

formalSeriesNeedDerivativeReceipts :
  FormalSinCosSeriesAutomaticallyGiveCoordinateDerivatives → ⊥
formalSeriesNeedDerivativeReceipts ()

record Status : Set where
  field
    genericPowerSeriesDerivativeSeamOwned : Bool
    polarTrigDerivativeInstanceOwned : Bool
    derivedSeriesConvergenceCompilerOwned : Bool
    sineDerivativeClosed : Bool
    cosineDerivativeClosed : Bool
    polarJacobianDerivativeEntriesClosed : Bool

    genericPowerSeriesDerivativeSeamOwnedIsTrue :
      genericPowerSeriesDerivativeSeamOwned ≡ true
    polarTrigDerivativeInstanceOwnedIsTrue : polarTrigDerivativeInstanceOwned ≡ true
    derivedSeriesConvergenceCompilerOwnedIsTrue :
      derivedSeriesConvergenceCompilerOwned ≡ true
    sineDerivativeClosedIsFalse : sineDerivativeClosed ≡ false
    cosineDerivativeClosedIsFalse : cosineDerivativeClosed ≡ false
    polarJacobianDerivativeEntriesClosedIsFalse :
      polarJacobianDerivativeEntriesClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { genericPowerSeriesDerivativeSeamOwned = true
  ; polarTrigDerivativeInstanceOwned = true
  ; derivedSeriesConvergenceCompilerOwned = true
  ; sineDerivativeClosed = false
  ; cosineDerivativeClosed = false
  ; polarJacobianDerivativeEntriesClosed = false
  ; genericPowerSeriesDerivativeSeamOwnedIsTrue = refl
  ; polarTrigDerivativeInstanceOwnedIsTrue = refl
  ; derivedSeriesConvergenceCompilerOwnedIsTrue = refl
  ; sineDerivativeClosedIsFalse = refl
  ; cosineDerivativeClosedIsFalse = refl
  ; polarJacobianDerivativeEntriesClosedIsFalse = refl
  }
