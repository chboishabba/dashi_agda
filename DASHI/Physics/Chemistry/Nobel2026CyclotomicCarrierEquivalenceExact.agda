module DASHI.Physics.Chemistry.Nobel2026CyclotomicCarrierEquivalenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as ChemistryPhase
import DASHI.Algebra.TriadicDepthOneCharacters as AtomicPhase
import DASHI.Biology.EisensteinThreeSixSymmetryExact as EisensteinPhase
import DASHI.Moonshine.C3FourierConjugationExact as Fourier
import DASHI.Moonshine.C3CyclotomicRealDescentExact as RealDescent
import DASHI.Moonshine.Monster3BPhaseTransportExact as Monster

------------------------------------------------------------------------
-- EXACT C3 CARRIER EQUIVALENCE
--
-- The live PR audit exposed independently developed exact three-phase carriers
-- used by chemistry, atomic/369 Fourier characters, Eisenstein arithmetic and
-- Moonshine/Monster transport.  This owner pays their literal finite
-- interoperability and action compatibility.  Only representation structure
-- transfers: molecular chirality, magnetic quantum number, Eisenstein
-- arithmetic and Monster sectors remain different semantics.
------------------------------------------------------------------------

chemToAtomic : ChemistryPhase.C3Phase → AtomicPhase.C3Phase
chemToAtomic ChemistryPhase.phaseOne = AtomicPhase.phase0
chemToAtomic ChemistryPhase.phaseZeta = AtomicPhase.phase1
chemToAtomic ChemistryPhase.phaseZetaSquared = AtomicPhase.phase2

atomicToChem : AtomicPhase.C3Phase → ChemistryPhase.C3Phase
atomicToChem AtomicPhase.phase0 = ChemistryPhase.phaseOne
atomicToChem AtomicPhase.phase1 = ChemistryPhase.phaseZeta
atomicToChem AtomicPhase.phase2 = ChemistryPhase.phaseZetaSquared

chemAtomicRoundTrip :
  (p : ChemistryPhase.C3Phase) → atomicToChem (chemToAtomic p) ≡ p
chemAtomicRoundTrip ChemistryPhase.phaseOne = refl
chemAtomicRoundTrip ChemistryPhase.phaseZeta = refl
chemAtomicRoundTrip ChemistryPhase.phaseZetaSquared = refl

atomicChemRoundTrip :
  (p : AtomicPhase.C3Phase) → chemToAtomic (atomicToChem p) ≡ p
atomicChemRoundTrip AtomicPhase.phase0 = refl
atomicChemRoundTrip AtomicPhase.phase1 = refl
atomicChemRoundTrip AtomicPhase.phase2 = refl

-- Chemistry's +1 phase advance is exactly multiplication by the canonical
-- atomic/Fourier generator phase1.
chemAdvanceIsAtomicGeneratorAction :
  (p : ChemistryPhase.C3Phase) →
  chemToAtomic (ChemistryPhase.phaseAdvance p)
  ≡ AtomicPhase.multiplyPhase AtomicPhase.phase1 (chemToAtomic p)
chemAdvanceIsAtomicGeneratorAction ChemistryPhase.phaseOne = refl
chemAdvanceIsAtomicGeneratorAction ChemistryPhase.phaseZeta = refl
chemAdvanceIsAtomicGeneratorAction ChemistryPhase.phaseZetaSquared = refl

chemConjugationIsAtomicConjugation :
  (p : ChemistryPhase.C3Phase) →
  chemToAtomic (ChemistryPhase.conjugatePhase p)
  ≡ AtomicPhase.conjugatePhase (chemToAtomic p)
chemConjugationIsAtomicConjugation ChemistryPhase.phaseOne = refl
chemConjugationIsAtomicConjugation ChemistryPhase.phaseZeta = refl
chemConjugationIsAtomicConjugation ChemistryPhase.phaseZetaSquared = refl

chemConjugationIsFourierInverse :
  (p : ChemistryPhase.C3Phase) →
  chemToAtomic (ChemistryPhase.conjugatePhase p)
  ≡ Fourier.inversePhase (chemToAtomic p)
chemConjugationIsFourierInverse ChemistryPhase.phaseOne = refl
chemConjugationIsFourierInverse ChemistryPhase.phaseZeta = refl
chemConjugationIsFourierInverse ChemistryPhase.phaseZetaSquared = refl

------------------------------------------------------------------------
-- Eisenstein phase carrier equivalence.
------------------------------------------------------------------------

chemToEisenstein : ChemistryPhase.C3Phase → EisensteinPhase.TernaryPhase
chemToEisenstein ChemistryPhase.phaseOne = EisensteinPhase.phaseOne
chemToEisenstein ChemistryPhase.phaseZeta = EisensteinPhase.phaseOmega
chemToEisenstein ChemistryPhase.phaseZetaSquared = EisensteinPhase.phaseOmegaSquared

eisensteinToChem : EisensteinPhase.TernaryPhase → ChemistryPhase.C3Phase
eisensteinToChem EisensteinPhase.phaseOne = ChemistryPhase.phaseOne
eisensteinToChem EisensteinPhase.phaseOmega = ChemistryPhase.phaseZeta
eisensteinToChem EisensteinPhase.phaseOmegaSquared = ChemistryPhase.phaseZetaSquared

chemEisensteinRoundTrip :
  (p : ChemistryPhase.C3Phase) → eisensteinToChem (chemToEisenstein p) ≡ p
chemEisensteinRoundTrip ChemistryPhase.phaseOne = refl
chemEisensteinRoundTrip ChemistryPhase.phaseZeta = refl
chemEisensteinRoundTrip ChemistryPhase.phaseZetaSquared = refl

eisensteinChemRoundTrip :
  (p : EisensteinPhase.TernaryPhase) → chemToEisenstein (eisensteinToChem p) ≡ p
eisensteinChemRoundTrip EisensteinPhase.phaseOne = refl
eisensteinChemRoundTrip EisensteinPhase.phaseOmega = refl
eisensteinChemRoundTrip EisensteinPhase.phaseOmegaSquared = refl

chemAdvanceIsEisensteinNext :
  (p : ChemistryPhase.C3Phase) →
  chemToEisenstein (ChemistryPhase.phaseAdvance p)
  ≡ EisensteinPhase.nextPhase (chemToEisenstein p)
chemAdvanceIsEisensteinNext ChemistryPhase.phaseOne = refl
chemAdvanceIsEisensteinNext ChemistryPhase.phaseZeta = refl
chemAdvanceIsEisensteinNext ChemistryPhase.phaseZetaSquared = refl

-- EisensteinThreeSixSymmetryExact did not need a named conjugation map, so the
-- exact reflection is supplied locally and welded to the other carriers.
eisensteinConjugate : EisensteinPhase.TernaryPhase → EisensteinPhase.TernaryPhase
eisensteinConjugate EisensteinPhase.phaseOne = EisensteinPhase.phaseOne
eisensteinConjugate EisensteinPhase.phaseOmega = EisensteinPhase.phaseOmegaSquared
eisensteinConjugate EisensteinPhase.phaseOmegaSquared = EisensteinPhase.phaseOmega

chemConjugationIsEisensteinConjugation :
  (p : ChemistryPhase.C3Phase) →
  chemToEisenstein (ChemistryPhase.conjugatePhase p)
  ≡ eisensteinConjugate (chemToEisenstein p)
chemConjugationIsEisensteinConjugation ChemistryPhase.phaseOne = refl
chemConjugationIsEisensteinConjugation ChemistryPhase.phaseZeta = refl
chemConjugationIsEisensteinConjugation ChemistryPhase.phaseZetaSquared = refl

atomicAndEisensteinAgreeThroughChemistry :
  (p : ChemistryPhase.C3Phase) →
  atomicToChem (chemToAtomic p) ≡ eisensteinToChem (chemToEisenstein p)
atomicAndEisensteinAgreeThroughChemistry ChemistryPhase.phaseOne = refl
atomicAndEisensteinAgreeThroughChemistry ChemistryPhase.phaseZeta = refl
atomicAndEisensteinAgreeThroughChemistry ChemistryPhase.phaseZetaSquared = refl

------------------------------------------------------------------------
-- Moonshine/Monster C3 conjugation and real-descent interoperability.
-- This consumes already-merged exact C3 owners also used by Ogg/SSP work.
------------------------------------------------------------------------

chemToMonster : ChemistryPhase.C3Phase → Monster.C3Phase
chemToMonster p = Fourier.phaseToMonster (chemToAtomic p)

chemConjugationIsMonsterInversion :
  (p : ChemistryPhase.C3Phase) →
  chemToMonster (ChemistryPhase.conjugatePhase p)
  ≡ Monster.transportPhase Monster.invertsGenerator (chemToMonster p)
chemConjugationIsMonsterInversion ChemistryPhase.phaseOne = refl
chemConjugationIsMonsterInversion ChemistryPhase.phaseZeta = refl
chemConjugationIsMonsterInversion ChemistryPhase.phaseZetaSquared = refl

chemConjugationOrbit : ChemistryPhase.C3Phase → RealDescent.C3ConjugationOrbit
chemConjugationOrbit p = RealDescent.conjugationOrbit (chemToAtomic p)

chemRealifiedSector : ChemistryPhase.C3Phase → RealDescent.RealifiedC3Sector
chemRealifiedSector p = RealDescent.realifiedSector (chemConjugationOrbit p)

chemFixedPhaseDescendsToRealAxis :
  chemRealifiedSector ChemistryPhase.phaseOne ≡ RealDescent.fixedRealAxis
chemFixedPhaseDescendsToRealAxis = refl

chemZetaPairDescendsToTransversePlane :
  chemRealifiedSector ChemistryPhase.phaseZeta
  ≡ RealDescent.transverseConjugatePlane
chemZetaPairDescendsToTransversePlane = refl

chemZetaSquaredPairDescendsToTransversePlane :
  chemRealifiedSector ChemistryPhase.phaseZetaSquared
  ≡ RealDescent.transverseConjugatePlane
chemZetaSquaredPairDescendsToTransversePlane = refl

chemTraceIsConjugationInvariant :
  (p : ChemistryPhase.C3Phase) →
  RealDescent.cyclotomicTrace
    (chemToAtomic (ChemistryPhase.conjugatePhase p))
  ≡ RealDescent.cyclotomicTrace (chemToAtomic p)
chemTraceIsConjugationInvariant ChemistryPhase.phaseOne = refl
chemTraceIsConjugationInvariant ChemistryPhase.phaseZeta = refl
chemTraceIsConjugationInvariant ChemistryPhase.phaseZetaSquared = refl

record CyclotomicCarrierEquivalenceBoundary : Set where
  constructor cyclotomicCarrierEquivalenceBoundary
  field
    chemistryAtomicCarrierBijectionPaid : Bool
    chemistryEisensteinCarrierBijectionPaid : Bool
    generatorActionIntertwinerPaid : Bool
    conjugationIntertwinerPaid : Bool
    moonshineMonsterConjugationIntertwinerPaid : Bool
    fixedPlusConjugatePairDescentPaid : Bool
    carrierEquivalenceIdentifiesPhysicalSemantics : Bool
    molecularChiralityIsMagneticQuantumNumber : Bool
    molecularChiralityIsEisensteinArithmeticObject : Bool
    molecularChiralityIsMonsterSector : Bool

canonicalCyclotomicCarrierEquivalenceBoundary : CyclotomicCarrierEquivalenceBoundary
canonicalCyclotomicCarrierEquivalenceBoundary =
  cyclotomicCarrierEquivalenceBoundary
    true true true true true true false false false false
