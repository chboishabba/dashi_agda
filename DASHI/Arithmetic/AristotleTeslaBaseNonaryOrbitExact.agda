module DASHI.Arithmetic.AristotleTeslaBaseNonaryOrbitExact where

------------------------------------------------------------------------
-- UPSTREAM ARISTOTLE SOURCE / ATTRIBUTION
--
-- Aristotle (Harmonic), editor of the user-supplied Lean project.
-- Source modules:
--   RequestProject.Tesla369
--   SHA-256 fdce91aae59877bbbc31dbc96ab86547debb0555e624bec365fd60d63d8faf10
--   RequestProject.BaseGeneral
--   SHA-256 dca43f7dfc6e664b7c3086dfec2bf75cf3085be29c66c67a20a6bd56b9a1edda
--
-- The upstream project README requests @Aristotle-Harmonic attribution and
-- the commit trailer
--   Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
--
-- PRIMARY MATHEMATICAL SOURCE
-- Elementary finite arithmetic on Z/9Z; no external DOI is asserted here.
--
-- DASHI CONTRIBUTION
-- Transport the exact finite residue content of the two Lean modules onto the
-- repository's existing NonaryTruth ring, rather than introducing a parallel
-- ZMod-9 carrier.  This closes the six-cycle / trinity exclusion / 1+2+6
-- vortex-orbit surface constructively by exhaustive finite reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_)

import DASHI.Foundations.Base369NonaryTruthRing as Ring

------------------------------------------------------------------------
-- The exact six-cycle of powers of two modulo nine.
------------------------------------------------------------------------

data Phase6 : Set where
  phase0 phase1 phase2 phase3 phase4 phase5 : Phase6

nextPhase : Phase6 → Phase6
nextPhase phase0 = phase1
nextPhase phase1 = phase2
nextPhase phase2 = phase3
nextPhase phase3 = phase4
nextPhase phase4 = phase5
nextPhase phase5 = phase0

phaseResidue : Phase6 → Ring.NonaryTruth
phaseResidue phase0 = Ring.non-1
phaseResidue phase1 = Ring.non-2
phaseResidue phase2 = Ring.non-4
phaseResidue phase3 = Ring.non-8
phaseResidue phase4 = Ring.non-7
phaseResidue phase5 = Ring.non-5

doubleResidue : Ring.NonaryTruth → Ring.NonaryTruth
doubleResidue x = Ring.nonaryMul Ring.non-2 x

phaseResidueAdvancesByDoubling :
  (phase : Phase6) →
  phaseResidue (nextPhase phase) ≡ doubleResidue (phaseResidue phase)
phaseResidueAdvancesByDoubling phase0 = refl
phaseResidueAdvancesByDoubling phase1 = refl
phaseResidueAdvancesByDoubling phase2 = refl
phaseResidueAdvancesByDoubling phase3 = refl
phaseResidueAdvancesByDoubling phase4 = refl
phaseResidueAdvancesByDoubling phase5 = refl

iteratePhase : Nat → Phase6 → Phase6
iteratePhase zero phase = phase
iteratePhase (suc n) phase = iteratePhase n (nextPhase phase)

phasePeriodSix : (phase : Phase6) → iteratePhase 6 phase ≡ phase
phasePeriodSix phase0 = refl
phasePeriodSix phase1 = refl
phasePeriodSix phase2 = refl
phasePeriodSix phase3 = refl
phasePeriodSix phase4 = refl
phasePeriodSix phase5 = refl

data PositiveOffsetBelowSix : Set where
  offset1 offset2 offset3 offset4 offset5 : PositiveOffsetBelowSix

offsetNat : PositiveOffsetBelowSix → Nat
offsetNat offset1 = 1
offsetNat offset2 = 2
offsetNat offset3 = 3
offsetNat offset4 = 4
offsetNat offset5 = 5

noPositiveStartPeriodBelowSix :
  (offset : PositiveOffsetBelowSix) →
  iteratePhase (offsetNat offset) phase0 ≡ phase0 →
  ⊥
noPositiveStartPeriodBelowSix offset1 ()
noPositiveStartPeriodBelowSix offset2 ()
noPositiveStartPeriodBelowSix offset3 ()
noPositiveStartPeriodBelowSix offset4 ()
noPositiveStartPeriodBelowSix offset5 ()

------------------------------------------------------------------------
-- Trinity residue shadow {0,3,6}; the six-cycle never enters it.
------------------------------------------------------------------------

data TriadicResidue : Ring.NonaryTruth → Set where
  residue0Triadic : TriadicResidue Ring.non-0
  residue3Triadic : TriadicResidue Ring.non-3
  residue6Triadic : TriadicResidue Ring.non-6

phaseResidueNeverTriadic :
  (phase : Phase6) →
  TriadicResidue (phaseResidue phase) →
  ⊥
phaseResidueNeverTriadic phase0 ()
phaseResidueNeverTriadic phase1 ()
phaseResidueNeverTriadic phase2 ()
phaseResidueNeverTriadic phase3 ()
phaseResidueNeverTriadic phase4 ()
phaseResidueNeverTriadic phase5 ()

doubleThreeIsSix : doubleResidue Ring.non-3 ≡ Ring.non-6
doubleThreeIsSix = refl

doubleSixIsThree : doubleResidue Ring.non-6 ≡ Ring.non-3
doubleSixIsThree = refl

doubleZeroIsZero : doubleResidue Ring.non-0 ≡ Ring.non-0
doubleZeroIsZero = refl

threeSquaredIsZeroModNine :
  Ring.nonaryMul Ring.non-3 Ring.non-3 ≡ Ring.non-0
threeSquaredIsZeroModNine = refl

------------------------------------------------------------------------
-- BaseGeneral's three doubling-orbit species: 1 + 2 + 6 = 9.
------------------------------------------------------------------------

data DoublingOrbitClass : Set where
  zeroOrbit triadicOrbit unitOrbit : DoublingOrbitClass

vortexClass : Ring.NonaryTruth → DoublingOrbitClass
vortexClass Ring.non-0 = zeroOrbit
vortexClass Ring.non-1 = unitOrbit
vortexClass Ring.non-2 = unitOrbit
vortexClass Ring.non-3 = triadicOrbit
vortexClass Ring.non-4 = unitOrbit
vortexClass Ring.non-5 = unitOrbit
vortexClass Ring.non-6 = triadicOrbit
vortexClass Ring.non-7 = unitOrbit
vortexClass Ring.non-8 = unitOrbit

doublingPreservesVortexClass :
  (residue : Ring.NonaryTruth) →
  vortexClass (doubleResidue residue) ≡ vortexClass residue
doublingPreservesVortexClass Ring.non-0 = refl
doublingPreservesVortexClass Ring.non-1 = refl
doublingPreservesVortexClass Ring.non-2 = refl
doublingPreservesVortexClass Ring.non-3 = refl
doublingPreservesVortexClass Ring.non-4 = refl
doublingPreservesVortexClass Ring.non-5 = refl
doublingPreservesVortexClass Ring.non-6 = refl
doublingPreservesVortexClass Ring.non-7 = refl
doublingPreservesVortexClass Ring.non-8 = refl

phaseResidueIsUnitOrbit :
  (phase : Phase6) →
  vortexClass (phaseResidue phase) ≡ unitOrbit
phaseResidueIsUnitOrbit phase0 = refl
phaseResidueIsUnitOrbit phase1 = refl
phaseResidueIsUnitOrbit phase2 = refl
phaseResidueIsUnitOrbit phase3 = refl
phaseResidueIsUnitOrbit phase4 = refl
phaseResidueIsUnitOrbit phase5 = refl

unitOrbitExactlySixCycle :
  (residue : Ring.NonaryTruth) →
  vortexClass residue ≡ unitOrbit →
  Σ Phase6 (λ phase → phaseResidue phase ≡ residue)
unitOrbitExactlySixCycle Ring.non-0 ()
unitOrbitExactlySixCycle Ring.non-1 proof = phase0 , refl
unitOrbitExactlySixCycle Ring.non-2 proof = phase1 , refl
unitOrbitExactlySixCycle Ring.non-3 ()
unitOrbitExactlySixCycle Ring.non-4 proof = phase2 , refl
unitOrbitExactlySixCycle Ring.non-5 proof = phase5 , refl
unitOrbitExactlySixCycle Ring.non-6 ()
unitOrbitExactlySixCycle Ring.non-7 proof = phase4 , refl
unitOrbitExactlySixCycle Ring.non-8 proof = phase3 , refl

orbitClassCardinality : DoublingOrbitClass → Nat
orbitClassCardinality zeroOrbit = 1
orbitClassCardinality triadicOrbit = 2
orbitClassCardinality unitOrbit = 6

orbitCardinalitiesSumToNine :
  orbitClassCardinality zeroOrbit
  + orbitClassCardinality triadicOrbit
  + orbitClassCardinality unitOrbit
  ≡ 9
orbitCardinalitiesSumToNine = refl

record AristotleTeslaBaseNonaryBoundary : Set where
  field
    exactSixCycleConstructed : Bool
    exactSixCycleConstructedIsTrue : exactSixCycleConstructed ≡ true
    noSmallerPositiveStartPeriod : Bool
    noSmallerPositiveStartPeriodIsTrue : noSmallerPositiveStartPeriod ≡ true
    sixCycleAvoidsTriadicResidues : Bool
    sixCycleAvoidsTriadicResiduesIsTrue : sixCycleAvoidsTriadicResidues ≡ true
    vortexOrbitPartitionOneTwoSix : Bool
    vortexOrbitPartitionOneTwoSixIsTrue : vortexOrbitPartitionOneTwoSix ≡ true

canonicalAristotleTeslaBaseNonaryBoundary : AristotleTeslaBaseNonaryBoundary
canonicalAristotleTeslaBaseNonaryBoundary = record
  { exactSixCycleConstructed = true
  ; exactSixCycleConstructedIsTrue = refl
  ; noSmallerPositiveStartPeriod = true
  ; noSmallerPositiveStartPeriodIsTrue = refl
  ; sixCycleAvoidsTriadicResidues = true
  ; sixCycleAvoidsTriadicResiduesIsTrue = refl
  ; vortexOrbitPartitionOneTwoSix = true
  ; vortexOrbitPartitionOneTwoSixIsTrue = refl
  }
