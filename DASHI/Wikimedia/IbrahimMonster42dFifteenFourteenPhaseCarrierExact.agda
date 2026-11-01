module DASHI.Wikimedia.IbrahimMonster42dFifteenFourteenPhaseCarrierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_)
open import Data.Product using (_,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as SSP15
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Wikimedia.IbrahimMonster42d17496PositiveBridgeAcquisitionExact as Bridge
import DASHI.Wikimedia.IbrahimMonsterTernary27PhasePreservingFiveOrbitReductionExact as Reduction

------------------------------------------------------------------------
-- MONSTER 42d / TERNARY27 -> FIFTEEN -> FOURTEEN -> FORTY-TWO CARRIER
--
-- The primary 15-state construction is now source-bound to the exact
-- phase-preserving ternary-27 symmetry reduction:
--
--   T^3 = T x T^2
--       -> T x (T^2 / inner global inversion)
--       = 3 x 5
--       = 15.
--
-- The repository also owns two finite structures built from the same
-- five-mode/D4-label family:
--
--   * five modes x three balanced phases = 15 (SSP15),
--   * five D4 labels x two binary orientations = 10.
--
-- Hence 15 = 5 + 10 is retained as a secondary decomposition of the same
-- five-mode phase carrier: five neutral phase states plus ten non-neutral
-- oriented states.  Then:
--
--   14 = 15 - one distinguished neutral lane,
--   42 = 3 * 14.
--
-- The 14-state residual is an explicit list of the canonical SSP15 lanes with
-- only (mode09, zeroTrit) omitted.  The map from the five inner inversion
-- orbits to ComplementMode5 is an indexing bijection only; it is not a D4 or
-- Monster semantic identity.  Likewise no direct 27 -> 5 selector is claimed.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Exact phase-preserving 27 -> 3 x 5 source.
------------------------------------------------------------------------

ternary27ReductionBoundary : Reduction.Ternary27ReductionBoundary
ternary27ReductionBoundary = Reduction.currentTernary27ReductionBoundary

phaseOrbit15ToSSP15RoundTrip :
  (lane : Reduction.PhaseOrbit15) →
  Reduction.ssp15ToPhaseOrbit (Reduction.phaseOrbitToSSP15 lane) ≡ lane
phaseOrbit15ToSSP15RoundTrip = Reduction.phaseOrbitSSP15RoundTrip

ssp15ToPhaseOrbit15RoundTrip :
  (lane : SSP15.SSP15InternalLane) →
  Reduction.phaseOrbitToSSP15 (Reduction.ssp15ToPhaseOrbit lane) ≡ lane
ssp15ToPhaseOrbit15RoundTrip = Reduction.ssp15PhaseOrbitRoundTrip

------------------------------------------------------------------------
-- 2. Exact five-mode and ten-oriented carrier counts.
------------------------------------------------------------------------

canonicalFiveModes : List Five.D4IrreducibleType
canonicalFiveModes =
  Five.A1 ∷ Five.A2 ∷ Five.B1 ∷ Five.B2 ∷ Five.E ∷ []

canonicalTenOrientedModes : List Five.OrientedMode
canonicalTenOrientedModes =
  Five.orientedMode Five.A1 Five.negativeOrientation
  ∷ Five.orientedMode Five.A1 Five.positiveOrientation
  ∷ Five.orientedMode Five.A2 Five.negativeOrientation
  ∷ Five.orientedMode Five.A2 Five.positiveOrientation
  ∷ Five.orientedMode Five.B1 Five.negativeOrientation
  ∷ Five.orientedMode Five.B1 Five.positiveOrientation
  ∷ Five.orientedMode Five.B2 Five.negativeOrientation
  ∷ Five.orientedMode Five.B2 Five.positiveOrientation
  ∷ Five.orientedMode Five.E Five.negativeOrientation
  ∷ Five.orientedMode Five.E Five.positiveOrientation
  ∷ []

fiveModeCountIsFive : SSP15.listCount canonicalFiveModes ≡ 5
fiveModeCountIsFive = refl

tenOrientedCountIsTen : SSP15.listCount canonicalTenOrientedModes ≡ 10
tenOrientedCountIsTen = refl

fivePlusTenIsFifteen :
  SSP15.listCount canonicalFiveModes
  + SSP15.listCount canonicalTenOrientedModes
  ≡ 15
fivePlusTenIsFifteen = refl

ssp15SourceCountIsFifteen :
  SSP15.listCount SSP15.canonicalSSP15InternalLanes ≡ 15
ssp15SourceCountIsFifteen = SSP15.ssp15InternalLaneCountIsFifteen

fiveTimesThreeSourceCountIsFifteen : 5 * 3 ≡ 15
fiveTimesThreeSourceCountIsFifteen = SSP15.fiveModesTimesThreePhasesIsFifteen

------------------------------------------------------------------------
-- 3. Delete the distinguished neutral lane from the canonical SSP15 carrier.
------------------------------------------------------------------------

distinguishedNeutralLane : SSP15.SSP15InternalLane
distinguishedNeutralLane = Quotient.mode09 , Harmonic.zeroTrit

canonicalResidual14 : List SSP15.SSP15InternalLane
canonicalResidual14 =
  (Quotient.mode09 , Harmonic.negativeTrit)
  ∷ (Quotient.mode09 , Harmonic.positiveTrit)
  ∷ (Quotient.mode18 , Harmonic.negativeTrit)
  ∷ (Quotient.mode18 , Harmonic.zeroTrit)
  ∷ (Quotient.mode18 , Harmonic.positiveTrit)
  ∷ (Quotient.mode27 , Harmonic.negativeTrit)
  ∷ (Quotient.mode27 , Harmonic.zeroTrit)
  ∷ (Quotient.mode27 , Harmonic.positiveTrit)
  ∷ (Quotient.mode36 , Harmonic.negativeTrit)
  ∷ (Quotient.mode36 , Harmonic.zeroTrit)
  ∷ (Quotient.mode36 , Harmonic.positiveTrit)
  ∷ (Quotient.mode45 , Harmonic.negativeTrit)
  ∷ (Quotient.mode45 , Harmonic.zeroTrit)
  ∷ (Quotient.mode45 , Harmonic.positiveTrit)
  ∷ []

residualLaneCountIsFourteen :
  SSP15.listCount canonicalResidual14 ≡ 14
residualLaneCountIsFourteen = refl

distinguishedPlusResidualIsFifteen :
  1 + SSP15.listCount canonicalResidual14
  ≡ SSP15.listCount SSP15.canonicalSSP15InternalLanes
distinguishedPlusResidualIsFifteen = refl

------------------------------------------------------------------------
-- 4. Outer balanced ternary phase gives the 42-count candidate.
------------------------------------------------------------------------

outerBalancedPhaseCount : Nat
outerBalancedPhaseCount = 3

outerThreeTimesFourteenArithmetic :
  outerBalancedPhaseCount * SSP15.listCount canonicalResidual14 ≡ 42
outerThreeTimesFourteenArithmetic = refl

------------------------------------------------------------------------
-- 5. 42d acquisition anchor.
------------------------------------------------------------------------

monster42dBridgeBoundary : Bridge.Monster42d17496BridgeBoundary
monster42dBridgeBoundary = Bridge.currentMonster42d17496BridgeBoundary

------------------------------------------------------------------------
-- 6. WrongType firewalls.
------------------------------------------------------------------------

data FortyTwoCarrierCreatesMonster42dSameObject : Set where
data FifteenMinusOneCreates42dAction : Set where
data TwentySevenCreatesFiveModeSelection : Set where

fortyTwoCarrierDoesNotCreateMonster42dSameObject :
  FortyTwoCarrierCreatesMonster42dSameObject → ⊥
fortyTwoCarrierDoesNotCreateMonster42dSameObject ()

fifteenMinusOneDoesNotCreate42dAction :
  FifteenMinusOneCreates42dAction → ⊥
fifteenMinusOneDoesNotCreate42dAction ()

twentySevenDoesNotCreateFiveModeSelection :
  TwentySevenCreatesFiveModeSelection → ⊥
twentySevenDoesNotCreateFiveModeSelection ()

------------------------------------------------------------------------
-- 7. Positive carrier frontier.
------------------------------------------------------------------------

record Monster42dFifteenFourteenBoundary : Set where
  constructor monster42d-fifteen-fourteen-boundary
  field
    ternary27PhasePreservingReductionSourcePaid : Bool
    twentySevenToThreeTimesFiveSymmetryReductionPaid : Bool
    ssp15FifteenLaneSourcePaid : Bool
    fiveModeSourcePaid : Bool
    tenOrientedCarrierSourcePaid : Bool
    fivePlusTenCarrierDecompositionPaid : Bool
    distinguishedNeutralDeletionLeavesFourteen : Bool
    outerThreeTimesFourteenIsFortyTwo : Bool
    a058678Monster42dSourcePaid : Bool
    positiveCarrierCorrelationRetained : Bool
    twentySevenToFiveModeSelectionPaid : Bool
    fortyTwoCarrierIsMonster42dSameObject : Bool
    fortyTwoCarrierCreatesMonster42dAction : Bool
    nextResidual : String
open Monster42dFifteenFourteenBoundary public

currentMonster42dFifteenFourteenBoundary :
  Monster42dFifteenFourteenBoundary
currentMonster42dFifteenFourteenBoundary =
  monster42d-fifteen-fourteen-boundary
    true true true true true true true true true true
    false false false
    "The 15-state carrier is now source-bound to the exact phase-preserving symmetry reduction T^3 -> T x (T^2/inner inversion) = 3 x 5 = 15, and to the existing SSP15 carrier by a two-sided finite indexing. Retain 5 + 10 = 15 as the neutral/non-neutral decomposition, the explicit deletion of one neutral mode09 lane to 14, and the outer 3 x 14 = 42 carrier as positive Monster42d acquisition structure. A direct 27 -> 5 selector remains false: the paid quotient preserves the outer ternary phase. The remaining proof-bearing debt is a Monster-theoretic bridge from this 42-state carrier to the selected class-42d graded action; neither the arithmetic nor A058678 supplies that action."
