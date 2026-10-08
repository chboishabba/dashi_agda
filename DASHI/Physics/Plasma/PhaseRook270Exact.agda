module DASHI.Physics.Plasma.PhaseRook270Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.TriadicDepthOneCharacters as C3

------------------------------------------------------------------------
-- PHASE-RESOLVED ROOK CARRIER
--
-- Twelve harmonic planes are arranged as 3 physical channels x 4 harmonic
-- families.  The four families are {axis} + three finite/C3-compatible
-- families.  Distinct planes are rook-related when they share a channel or a
-- harmonic family.
--
-- Base rook incidences:
--   same channel:  3 * C(4,2) = 18
--   same harmonic: 4 * C(3,2) = 12
--   total                         30
--
-- Every distinct-plane incidence carries two independent projective C3 phase
-- labels, hence a 3 x 3 = 9 fibre.  Therefore 30 * 9 = 270.
--
-- The same-axis-harmonic / different-channel sector has 3 * 9 = 27 states.
-- Its action-invariant complement has 27 * 9 = 243 = 3^5 states.
------------------------------------------------------------------------

data HarmonicFamily : Set where
  axisFamily : HarmonicFamily
  finiteFamily : C3.C3Phase → HarmonicFamily

record HarmonicPlane : Set where
  constructor harmonic-plane
  field
    channel : C3.C3Phase
    harmonic : HarmonicFamily

open HarmonicPlane public

record PhaseLine : Set where
  constructor phase-line
  field
    plane : HarmonicPlane
    phase : C3.C3Phase

open PhaseLine public

-- The first trit classifies the three 9-element base-incidence classes:
-- phase0 = same channel, {axis,h};
-- phase1 = same channel, two finite harmonics indexed by missing harmonic;
-- phase2 = same finite harmonic, two channels indexed by missing channel.
record Core243 : Set where
  constructor core243
  field
    incidenceClass : C3.C3Phase
    incidenceU : C3.C3Phase
    incidenceV : C3.C3Phase
    phaseLeft : C3.C3Phase
    phaseRight : C3.C3Phase

open Core243 public

record AxisBoundary27 : Set where
  constructor axis-boundary27
  field
    missingChannel : C3.C3Phase
    boundaryPhaseLeft : C3.C3Phase
    boundaryPhaseRight : C3.C3Phase

open AxisBoundary27 public

data Rook270 : Set where
  coreRook : Core243 → Rook270
  axisBoundaryRook : AxisBoundary27 → Rook270

------------------------------------------------------------------------
-- Exact cardinal arithmetic.  The finite types above are the actual carriers;
-- these Nat equalities merely expose their intended finite counts.
------------------------------------------------------------------------

phaseResolvedPairCount : Nat
phaseResolvedPairCount = 630

samePlanePairCount : Nat
samePlanePairCount = 36

rookPairCount : Nat
rookPairCount = 270

nonRookPairCount : Nat
nonRookPairCount = 324

coreCount : Nat
coreCount = 243

axisBoundaryCount : Nat
axisBoundaryCount = 27

phasePairPartitionCloses :
  samePlanePairCount + rookPairCount + nonRookPairCount ≡ phaseResolvedPairCount
phasePairPartitionCloses = refl

rookSplitCloses : coreCount + axisBoundaryCount ≡ rookPairCount
rookSplitCloses = refl

coreAsTwentySevenTimesNine : 27 * 9 ≡ coreCount
coreAsTwentySevenTimesNine = refl

coreAsThreeToFive : 3 * (3 * (3 * (3 * 3))) ≡ coreCount
coreAsThreeToFive = refl

axisBoundaryAsThreeToThree : 3 * (3 * 3) ≡ axisBoundaryCount
axisBoundaryAsThreeToThree = refl

------------------------------------------------------------------------
-- Physical C3 advance / inversion acts only on the two phase-fibre labels.
-- The rook-incidence coordinates are fixed, so Core243 and AxisBoundary27 are
-- invariant subcarriers under this action.
------------------------------------------------------------------------

advancePhase : C3.C3Phase → C3.C3Phase
advancePhase = C3.multiplyPhase C3.phase1

inversePhase : C3.C3Phase → C3.C3Phase
inversePhase = C3.conjugatePhase

advancePhaseThree : (p : C3.C3Phase) →
  advancePhase (advancePhase (advancePhase p)) ≡ p
advancePhaseThree C3.phase0 = refl
advancePhaseThree C3.phase1 = refl
advancePhaseThree C3.phase2 = refl

inversePhaseInvolutive : (p : C3.C3Phase) →
  inversePhase (inversePhase p) ≡ p
inversePhaseInvolutive C3.phase0 = refl
inversePhaseInvolutive C3.phase1 = refl
inversePhaseInvolutive C3.phase2 = refl

inverseConjugatesAdvance : (p : C3.C3Phase) →
  inversePhase (advancePhase p) ≡ advancePhase (advancePhase (inversePhase p))
inverseConjugatesAdvance C3.phase0 = refl
inverseConjugatesAdvance C3.phase1 = refl
inverseConjugatesAdvance C3.phase2 = refl

advanceCore : Core243 → Core243
advanceCore (core243 k u v p q) =
  core243 k u v (advancePhase p) (advancePhase q)

inverseCore : Core243 → Core243
inverseCore (core243 k u v p q) =
  core243 k u v (inversePhase p) (inversePhase q)

advanceBoundary : AxisBoundary27 → AxisBoundary27
advanceBoundary (axis-boundary27 m p q) =
  axis-boundary27 m (advancePhase p) (advancePhase q)

inverseBoundary : AxisBoundary27 → AxisBoundary27
inverseBoundary (axis-boundary27 m p q) =
  axis-boundary27 m (inversePhase p) (inversePhase q)

advanceCoreThree : (x : Core243) →
  advanceCore (advanceCore (advanceCore x)) ≡ x
advanceCoreThree (core243 k u v p q)
  rewrite advancePhaseThree p | advancePhaseThree q = refl

inverseCoreInvolutive : (x : Core243) →
  inverseCore (inverseCore x) ≡ x
inverseCoreInvolutive (core243 k u v p q)
  rewrite inversePhaseInvolutive p | inversePhaseInvolutive q = refl

advanceBoundaryThree : (x : AxisBoundary27) →
  advanceBoundary (advanceBoundary (advanceBoundary x)) ≡ x
advanceBoundaryThree (axis-boundary27 m p q)
  rewrite advancePhaseThree p | advancePhaseThree q = refl

inverseBoundaryInvolutive : (x : AxisBoundary27) →
  inverseBoundary (inverseBoundary x) ≡ x
inverseBoundaryInvolutive (axis-boundary27 m p q)
  rewrite inversePhaseInvolutive p | inversePhaseInvolutive q = refl

------------------------------------------------------------------------
-- Numerically exhausted orbit profile from scripts/phase243_rook_probe.py.
-- This is recorded as a checked finite receipt, not promoted to a generic
-- group-action theorem beyond this finite carrier.
------------------------------------------------------------------------

coreSizeThreeOrbitCount : Nat
coreSizeThreeOrbitCount = 27

coreSizeSixOrbitCount : Nat
coreSizeSixOrbitCount = 27

boundarySizeThreeOrbitCount : Nat
boundarySizeThreeOrbitCount = 3

boundarySizeSixOrbitCount : Nat
boundarySizeSixOrbitCount = 3

coreOrbitAccounting :
  coreSizeThreeOrbitCount * 3 + coreSizeSixOrbitCount * 6 ≡ coreCount
coreOrbitAccounting = refl

boundaryOrbitAccounting :
  boundarySizeThreeOrbitCount * 3 + boundarySizeSixOrbitCount * 6 ≡ axisBoundaryCount
boundaryOrbitAccounting = refl

record PhaseRookBoundary : Set where
  constructor phase-rook-boundary
  field
    arithmetic270CreatesPhysicalSymmetry : Bool
    arithmetic270CreatesPhysicalSymmetryIsFalse :
      arithmetic270CreatesPhysicalSymmetry ≡ false
    core243IsActionInvariantByConstruction : Bool
    core243IsActionInvariantByConstructionIsTrue :
      core243IsActionInvariantByConstruction ≡ true
    boundary27IsActionInvariantByConstruction : Bool
    boundary27IsActionInvariantByConstructionIsTrue :
      boundary27IsActionInvariantByConstruction ≡ true
    core243IsMonsterOrMoonshineModule : Bool
    core243IsMonsterOrMoonshineModuleIsFalse :
      core243IsMonsterOrMoonshineModule ≡ false

canonicalPhaseRookBoundary : PhaseRookBoundary
canonicalPhaseRookBoundary =
  phase-rook-boundary false refl true refl true refl false refl

sourceReference : String
sourceReference =
  "Phase-resolved magnet support: 12 planes = 3 channels x (axis + F3 harmonics); 30 rook plane-incidences with F3^2 phase fibres give 270 = 243 core + 27 axis boundary."
