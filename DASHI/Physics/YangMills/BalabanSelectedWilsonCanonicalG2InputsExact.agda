module DASHI.Physics.YangMills.BalabanSelectedWilsonCanonicalG2InputsExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius Functions",
-- Z. Wahrscheinlichkeitstheorie verw. Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Remove the last arbitrary source-covector seam from the canonical G2 input.
-- The source is definitionally the literal basis-evaluated Wilson first
-- variation of the selected plaquette.  Its four-bond support is supplied by
-- the existing exact Wilson theorem, hence the same sixteen subset projectors
-- generate both source and raw-extractor defect partials before the Möbius
-- transform.
--
-- The remaining inputs below are genuinely distinct physical data:
-- raw-localisation values/reconstruction and owner classification.  This file
-- does not manufacture their quantitative estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact as WilsonSource

record LiteralWilsonCanonicalG2RawInputs
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    (background : Plaquette.RationalSU2Background4)
    (bondField : Physical.PhysicalSU2BondField4)
    (plaquette : Plaquette.Plaquette4) : Set₁ where
  field
    rawLocalization : ℚ
    rawLocalizationAtom : Cube.Subset4 → ℚ
    rawLocalizationReconstruct :
      Sums.sumRational Cube.nonemptySubsets4 rawLocalizationAtom
      ≡ rawLocalization

    rawOwnerOf : Cube.Subset4 → Ownership.CorrelatedResidualOwner
    greenOwnerOf :
      Cube.Subset4 → Cube.Subset4 → Ownership.MultiplierGreenAtomOwner

open LiteralWilsonCanonicalG2RawInputs public

literalWilsonCanonicalG2Inputs :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {background bondField plaquette} →
  LiteralWilsonCanonicalG2RawInputs
    pseudoData background bondField plaquette →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    pseudoData
    (WilsonSource.plaquetteFirstVariationCovector background plaquette)
    bondField plaquette
literalWilsonCanonicalG2Inputs
    {pseudoData = pseudoData}
    {background = background}
    {bondField = bondField}
    {plaquette = plaquette}
    inputs = record
  { Canonical.CanonicalSubsetCorrelatedAuthorityInputs.sourceSupported =
      WilsonSource.plaquetteFirstVariationSupported background plaquette
  ; Canonical.CanonicalSubsetCorrelatedAuthorityInputs.rawLocalization =
      rawLocalization inputs
  ; Canonical.CanonicalSubsetCorrelatedAuthorityInputs.rawLocalizationAtom =
      rawLocalizationAtom inputs
  ; Canonical.CanonicalSubsetCorrelatedAuthorityInputs.rawLocalizationReconstruct =
      rawLocalizationReconstruct inputs
  ; Canonical.CanonicalSubsetCorrelatedAuthorityInputs.rawOwnerOf =
      rawOwnerOf inputs
  ; Canonical.CanonicalSubsetCorrelatedAuthorityInputs.greenOwnerOf =
      greenOwnerOf inputs
  }

literalWilsonCanonicalConstraintAtoms :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {background bondField plaquette}
    (inputs : LiteralWilsonCanonicalG2RawInputs
      pseudoData background bondField plaquette) →
  Canonical.canonicalConstraintAtoms
    (literalWilsonCanonicalG2Inputs inputs)
  ≡ Canonical.canonicalConstraintAtoms
    (literalWilsonCanonicalG2Inputs inputs)
literalWilsonCanonicalConstraintAtoms inputs = _≡_.refl

selectedWilsonCanonicalG2SourceLevel : ProofLevel
selectedWilsonCanonicalG2SourceLevel = machineChecked

-- The G2 source-support/subset/Möbius lane is now source-native.  Remaining
-- mathematics is the raw-localisation quantitative envelope and the selected
-- K+ / source-degree / defect-degree charge-relative bounds.
