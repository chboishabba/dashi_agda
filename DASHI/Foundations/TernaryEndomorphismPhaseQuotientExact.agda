module DASHI.Foundations.TernaryEndomorphismPhaseQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups", Graduate Texts in Mathematics 163,
-- Springer, 1996.
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- The repository already has the level-two ternary function carrier
--
--   ObservableLevelTwo = TriTruth -> TriTruth
--
-- and its lossless three-output code T^3.  This module equips that existing
-- 27-code carrier with the repository's order-three output phase.  The C3
-- action by postcomposition is free: every code has one and only one
-- representative whose low-input output is tri-low.
--
-- The normalized quotient therefore has 3^2 = 9 representatives.  Exactly
-- two normalized representatives have three distinct outputs (the reversible
-- unit sector), while the other seven are nonunit/collapsing representatives.
-- Hence the finite carrier factorization is exact:
--
--   27 = 3 * (2 + 7)
--   27 / C3 = 9 = 2 + 7.
--
-- This seven is a PHASE-QUOTIENT seven.  It is kept distinct from the seven
-- S3-conjugacy functional-graph shapes constructed in the companion module.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)

import Base369 as Base
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Cognition.RecursiveFibreTower as Tower

------------------------------------------------------------------------
-- Order-three output phase.
------------------------------------------------------------------------

rotateTriTwice : Base.TriTruth → Base.TriTruth
rotateTriTwice value = Base.rotateTri (Base.rotateTri value)

rotateTriThree : (value : Base.TriTruth) →
  Base.rotateTri (rotateTriTwice value) ≡ value
rotateTriThree Base.tri-low = refl
rotateTriThree Base.tri-mid = refl
rotateTriThree Base.tri-high = refl

rotateTriByPhase : Phase.Phase3 → Base.TriTruth → Base.TriTruth
rotateTriByPhase Phase.phase0 value = value
rotateTriByPhase Phase.phase1 value = Base.rotateTri value
rotateTriByPhase Phase.phase2 value = rotateTriTwice value

rotateOutputCode : Tower.LevelTwoCode → Tower.LevelTwoCode
rotateOutputCode (lowValue , (midValue , highValue)) =
  Base.rotateTri lowValue ,
  (Base.rotateTri midValue , Base.rotateTri highValue)

rotateOutputCodeThree :
  (code : Tower.LevelTwoCode) →
  rotateOutputCode (rotateOutputCode (rotateOutputCode code)) ≡ code
rotateOutputCodeThree
  (lowValue , (midValue , highValue))
  rewrite rotateTriThree lowValue
        | rotateTriThree midValue
        | rotateTriThree highValue = refl

rotateOutputCodeHasNoFixedPoint :
  (code : Tower.LevelTwoCode) →
  rotateOutputCode code ≡ code →
  ⊥
rotateOutputCodeHasNoFixedPoint (Base.tri-low , rest) ()
rotateOutputCodeHasNoFixedPoint (Base.tri-mid , rest) ()
rotateOutputCodeHasNoFixedPoint (Base.tri-high , rest) ()

PhaseQuotient9 : Set
PhaseQuotient9 = Base.TriTruth × Base.TriTruth

phaseEncode :
  Tower.LevelTwoCode → Phase.Phase3 × PhaseQuotient9
phaseEncode (Base.tri-low , (midValue , highValue)) =
  Phase.phase0 , (midValue , highValue)
phaseEncode (Base.tri-mid , (midValue , highValue)) =
  Phase.phase1 , (rotateTriTwice midValue , rotateTriTwice highValue)
phaseEncode (Base.tri-high , (midValue , highValue)) =
  Phase.phase2 , (Base.rotateTri midValue , Base.rotateTri highValue)

phaseDecode :
  Phase.Phase3 × PhaseQuotient9 → Tower.LevelTwoCode
phaseDecode (Phase.phase0 , (midValue , highValue)) =
  Base.tri-low , (midValue , highValue)
phaseDecode (Phase.phase1 , (midValue , highValue)) =
  Base.tri-mid , (Base.rotateTri midValue , Base.rotateTri highValue)
phaseDecode (Phase.phase2 , (midValue , highValue)) =
  Base.tri-high , (rotateTriTwice midValue , rotateTriTwice highValue)

phaseDecodeAfterEncode :
  (code : Tower.LevelTwoCode) →
  phaseDecode (phaseEncode code) ≡ code
phaseDecodeAfterEncode (Base.tri-low , (midValue , highValue)) = refl
phaseDecodeAfterEncode (Base.tri-mid , (midValue , highValue))
  rewrite rotateTriThree midValue | rotateTriThree highValue = refl
phaseDecodeAfterEncode (Base.tri-high , (midValue , highValue))
  rewrite rotateTriThree midValue | rotateTriThree highValue = refl

phaseEncodeAfterDecode :
  (phaseCode : Phase.Phase3 × PhaseQuotient9) →
  phaseEncode (phaseDecode phaseCode) ≡ phaseCode
phaseEncodeAfterDecode (Phase.phase0 , (midValue , highValue)) = refl
phaseEncodeAfterDecode (Phase.phase1 , (midValue , highValue))
  rewrite rotateTriThree midValue | rotateTriThree highValue = refl
phaseEncodeAfterDecode (Phase.phase2 , (midValue , highValue))
  rewrite rotateTriThree midValue | rotateTriThree highValue = refl

------------------------------------------------------------------------
-- The normalized 9-sector splits structurally as 2 reversible + 7 nonunit.
------------------------------------------------------------------------

data UnitPhase2 : Set where
  unitCyclic unitReflective : UnitPhase2

data NonUnitPhase7 : Set where
  nonUnitLowLow
    nonUnitLowMid
    nonUnitLowHigh
    nonUnitMidLow
    nonUnitMidMid
    nonUnitHighLow
    nonUnitHighHigh : NonUnitPhase7

PhaseClass9 : Set
PhaseClass9 = UnitPhase2 ⊎ NonUnitPhase7

classifyPhaseQuotient : PhaseQuotient9 → PhaseClass9
classifyPhaseQuotient (Base.tri-low , Base.tri-low) =
  inj₂ nonUnitLowLow
classifyPhaseQuotient (Base.tri-low , Base.tri-mid) =
  inj₂ nonUnitLowMid
classifyPhaseQuotient (Base.tri-low , Base.tri-high) =
  inj₂ nonUnitLowHigh
classifyPhaseQuotient (Base.tri-mid , Base.tri-low) =
  inj₂ nonUnitMidLow
classifyPhaseQuotient (Base.tri-mid , Base.tri-mid) =
  inj₂ nonUnitMidMid
classifyPhaseQuotient (Base.tri-mid , Base.tri-high) =
  inj₁ unitCyclic
classifyPhaseQuotient (Base.tri-high , Base.tri-low) =
  inj₂ nonUnitHighLow
classifyPhaseQuotient (Base.tri-high , Base.tri-mid) =
  inj₁ unitReflective
classifyPhaseQuotient (Base.tri-high , Base.tri-high) =
  inj₂ nonUnitHighHigh

forgetPhaseClass : PhaseClass9 → PhaseQuotient9
forgetPhaseClass (inj₁ unitCyclic) =
  Base.tri-mid , Base.tri-high
forgetPhaseClass (inj₁ unitReflective) =
  Base.tri-high , Base.tri-mid
forgetPhaseClass (inj₂ nonUnitLowLow) =
  Base.tri-low , Base.tri-low
forgetPhaseClass (inj₂ nonUnitLowMid) =
  Base.tri-low , Base.tri-mid
forgetPhaseClass (inj₂ nonUnitLowHigh) =
  Base.tri-low , Base.tri-high
forgetPhaseClass (inj₂ nonUnitMidLow) =
  Base.tri-mid , Base.tri-low
forgetPhaseClass (inj₂ nonUnitMidMid) =
  Base.tri-mid , Base.tri-mid
forgetPhaseClass (inj₂ nonUnitHighLow) =
  Base.tri-high , Base.tri-low
forgetPhaseClass (inj₂ nonUnitHighHigh) =
  Base.tri-high , Base.tri-high

forgetAfterClassify :
  (pair : PhaseQuotient9) →
  forgetPhaseClass (classifyPhaseQuotient pair) ≡ pair
forgetAfterClassify (Base.tri-low , Base.tri-low) = refl
forgetAfterClassify (Base.tri-low , Base.tri-mid) = refl
forgetAfterClassify (Base.tri-low , Base.tri-high) = refl
forgetAfterClassify (Base.tri-mid , Base.tri-low) = refl
forgetAfterClassify (Base.tri-mid , Base.tri-mid) = refl
forgetAfterClassify (Base.tri-mid , Base.tri-high) = refl
forgetAfterClassify (Base.tri-high , Base.tri-low) = refl
forgetAfterClassify (Base.tri-high , Base.tri-mid) = refl
forgetAfterClassify (Base.tri-high , Base.tri-high) = refl

classifyAfterForget :
  (phaseClass : PhaseClass9) →
  classifyPhaseQuotient (forgetPhaseClass phaseClass) ≡ phaseClass
classifyAfterForget (inj₁ unitCyclic) = refl
classifyAfterForget (inj₁ unitReflective) = refl
classifyAfterForget (inj₂ nonUnitLowLow) = refl
classifyAfterForget (inj₂ nonUnitLowMid) = refl
classifyAfterForget (inj₂ nonUnitLowHigh) = refl
classifyAfterForget (inj₂ nonUnitMidLow) = refl
classifyAfterForget (inj₂ nonUnitMidMid) = refl
classifyAfterForget (inj₂ nonUnitHighLow) = refl
classifyAfterForget (inj₂ nonUnitHighHigh) = refl

------------------------------------------------------------------------
-- Full 27 = phase3 x (unit2 + nonunit7) factorization.
------------------------------------------------------------------------

Factorized27 : Set
Factorized27 = Phase.Phase3 × PhaseClass9

factorize27 : Tower.LevelTwoCode → Factorized27
factorize27 code =
  proj₁ (phaseEncode code) ,
  classifyPhaseQuotient (proj₂ (phaseEncode code))

unfactorize27 : Factorized27 → Tower.LevelTwoCode
unfactorize27 (phase , phaseClass) =
  phaseDecode (phase , forgetPhaseClass phaseClass)

unfactorizeAfterFactorize :
  (code : Tower.LevelTwoCode) →
  unfactorize27 (factorize27 code) ≡ code
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
unfactorizeAfterFactorize (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

factorizeAfterUnfactorize :
  (factorized : Factorized27) →
  factorize27 (unfactorize27 factorized) ≡ factorized
factorizeAfterUnfactorize (Phase.phase0 , inj₁ unitCyclic) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₁ unitReflective) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitLowLow) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitLowMid) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitLowHigh) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitMidLow) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitMidMid) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitHighLow) = refl
factorizeAfterUnfactorize (Phase.phase0 , inj₂ nonUnitHighHigh) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₁ unitCyclic) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₁ unitReflective) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitLowLow) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitLowMid) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitLowHigh) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitMidLow) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitMidMid) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitHighLow) = refl
factorizeAfterUnfactorize (Phase.phase1 , inj₂ nonUnitHighHigh) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₁ unitCyclic) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₁ unitReflective) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitLowLow) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitLowMid) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitLowHigh) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitMidLow) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitMidMid) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitHighLow) = refl
factorizeAfterUnfactorize (Phase.phase2 , inj₂ nonUnitHighHigh) = refl

------------------------------------------------------------------------
-- The six unit codes are exactly phase3 x unit2.
------------------------------------------------------------------------

data PermutationCode6 : Tower.LevelTwoCode → Set where
  permutationLowMidHigh :
    PermutationCode6
      (Base.tri-low , (Base.tri-mid , Base.tri-high))
  permutationLowHighMid :
    PermutationCode6
      (Base.tri-low , (Base.tri-high , Base.tri-mid))
  permutationMidHighLow :
    PermutationCode6
      (Base.tri-mid , (Base.tri-high , Base.tri-low))
  permutationMidLowHigh :
    PermutationCode6
      (Base.tri-mid , (Base.tri-low , Base.tri-high))
  permutationHighLowMid :
    PermutationCode6
      (Base.tri-high , (Base.tri-low , Base.tri-mid))
  permutationHighMidLow :
    PermutationCode6
      (Base.tri-high , (Base.tri-mid , Base.tri-low))

factorizedUnitCode :
  Phase.Phase3 → UnitPhase2 → Tower.LevelTwoCode
factorizedUnitCode phase unit =
  unfactorize27 (phase , inj₁ unit)

factorizedUnitIsPermutation :
  (phase : Phase.Phase3) →
  (unit : UnitPhase2) →
  PermutationCode6 (factorizedUnitCode phase unit)
factorizedUnitIsPermutation Phase.phase0 unitCyclic =
  permutationLowMidHigh
factorizedUnitIsPermutation Phase.phase0 unitReflective =
  permutationLowHighMid
factorizedUnitIsPermutation Phase.phase1 unitCyclic =
  permutationMidHighLow
factorizedUnitIsPermutation Phase.phase1 unitReflective =
  permutationMidLowHigh
factorizedUnitIsPermutation Phase.phase2 unitCyclic =
  permutationHighLowMid
factorizedUnitIsPermutation Phase.phase2 unitReflective =
  permutationHighMidLow

------------------------------------------------------------------------
-- Exact cardinal ledger.
------------------------------------------------------------------------

phaseCardinality : Nat
phaseCardinality = 3

unitPhaseCardinality : Nat
unitPhaseCardinality = 2

nonUnitPhaseCardinality : Nat
nonUnitPhaseCardinality = 7

phaseQuotientCardinality : Nat
phaseQuotientCardinality =
  unitPhaseCardinality + nonUnitPhaseCardinality

factorizedCardinality : Nat
factorizedCardinality =
  phaseCardinality * phaseQuotientCardinality

phaseQuotientIsNine : phaseQuotientCardinality ≡ 9
phaseQuotientIsNine = refl

factorizedIsTwentySeven : factorizedCardinality ≡ 27
factorizedIsTwentySeven = refl

nonUnitSectorIsTwentyOne :
  phaseCardinality * nonUnitPhaseCardinality ≡ 21
nonUnitSectorIsTwentyOne = refl

unitSectorIsSix :
  phaseCardinality * unitPhaseCardinality ≡ 6
unitSectorIsSix = refl

twentySevenIsThreeTimesTwoPlusSeven :
  3 * (2 + 7) ≡ 27
twentySevenIsThreeTimesTwoPlusSeven = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record TernaryEndomorphismPhaseBoundary : Set where
  field
    phaseFactorizationConstructed : Bool
    phaseFactorizationConstructedIsTrue :
      phaseFactorizationConstructed ≡ true

    outputC3ActionIsFixedPointFree : Bool
    outputC3ActionIsFixedPointFreeIsTrue :
      outputC3ActionIsFixedPointFree ≡ true

    phaseSevenIdentifiedWithS3ConjugacySeven : Bool
    phaseSevenIdentifiedWithS3ConjugacySevenIsFalse :
      phaseSevenIdentifiedWithS3ConjugacySeven ≡ false

canonicalTernaryEndomorphismPhaseBoundary :
  TernaryEndomorphismPhaseBoundary
canonicalTernaryEndomorphismPhaseBoundary =
  record
    { phaseFactorizationConstructed = true
    ; phaseFactorizationConstructedIsTrue = refl
    ; outputC3ActionIsFixedPointFree = true
    ; outputC3ActionIsFixedPointFreeIsTrue = refl
    ; phaseSevenIdentifiedWithS3ConjugacySeven = false
    ; phaseSevenIdentifiedWithS3ConjugacySevenIsFalse = refl
    }
