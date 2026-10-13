module DASHI.Physics.Chemistry.Nobel2026CyclotomicCarrierEquivalenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.CyclotomicPhaseAmplitudeBoundaryExact as ChemistryPhase
import DASHI.Algebra.TriadicDepthOneCharacters as AtomicPhase
import DASHI.Biology.EisensteinThreeSixSymmetryExact as EisensteinPhase

------------------------------------------------------------------------
-- EXACT C3 CARRIER EQUIVALENCE
--
-- The live PR audit exposed three independently developed exact three-phase
-- carriers used by chemistry, atomic/369 Fourier characters, and Eisenstein
-- arithmetic.  This owner pays their literal finite equivalence and action
-- compatibility.  It transfers representation structure only; it does not
-- identify molecular chirality, magnetic quantum number, or Eisenstein number
-- theory as one physical object.
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

-- Chemistry's +1 phase advance is exactly multiplication by the atomic
-- character generator phase1.
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
-- exact reflection is supplied locally and welded to the other two carriers.
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

record CyclotomicCarrierEquivalenceBoundary : Set where
  constructor cyclotomicCarrierEquivalenceBoundary
  field
    chemistryAtomicCarrierBijectionPaid : Bool
    chemistryEisensteinCarrierBijectionPaid : Bool
    generatorActionIntertwinerPaid : Bool
    conjugationIntertwinerPaid : Bool
    carrierEquivalenceIdentifiesPhysicalSemantics : Bool
    molecularChiralityIsMagneticQuantumNumber : Bool
    molecularChiralityIsEisensteinArithmeticObject : Bool

canonicalCyclotomicCarrierEquivalenceBoundary : CyclotomicCarrierEquivalenceBoundary
canonicalCyclotomicCarrierEquivalenceBoundary =
  cyclotomicCarrierEquivalenceBoundary
    true true true true false false false
