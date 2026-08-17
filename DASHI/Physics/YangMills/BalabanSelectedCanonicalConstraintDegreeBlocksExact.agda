module DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger Penrose, "A Generalized Inverse for Matrices", Proceedings of the
-- Cambridge Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Gian-Carlo Rota, "On the Foundations of Combinatorial Theory I. Theory of
-- Möbius Functions", Zeitschrift für Wahrscheinlichkeitstheorie und
-- Verwandte Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- Round57 had two independently useful facts:
--
--   (1) the selected residual authority is generated canonically from the same
--       sixteen subset projectors through the literal KKT constraint and
--       Boolean-four-cube Möbius inversion;
--   (2) every correlated residual family decomposes exactly into four raw and
--       sixteen Green degree blocks.
--
-- This file welds them on the SAME authority object.  The grouped quantities
-- consumed by the Round58 interval producer are therefore not caller-chosen
-- surrogates: they are definitionally the degree sums of the canonical family
-- built from the literal subset/KKT data.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

canonicalFamily :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector : KKT.StateVector}
    {bondField : Physical.PhysicalSU2BondField4}
    {plaquette : Plaquette.Plaquette4} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    pseudoData firstVariationCovector bondField plaquette →
  DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact.CorrelatedResidualFamily
canonicalFamily inputs =
  Authority.canonicalCorrelatedResidualFamily
    (Canonical.canonicalCorrelatedResidualAuthority inputs)

canonicalRawDegreeBlock :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → ℚ
canonicalRawDegreeBlock inputs = Degree.rawDegreeBlock (canonicalFamily inputs)

canonicalGreenDegreeBlock :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
canonicalGreenDegreeBlock inputs = Degree.greenDegreeBlock (canonicalFamily inputs)

canonicalCorrelatedResidualAsDegreeExpression :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector : KKT.StateVector}
    {bondField : Physical.PhysicalSU2BondField4}
    {plaquette : Plaquette.Plaquette4}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Authority.canonicalMultiplierGreenPairing
      pseudoData firstVariationCovector
      (Boundary.rawPlaquetteSingletonExtractor bondField plaquette)
  ≡ Canonical.rawLocalization inputs
      - Degree.greenDegreeTotal (canonicalFamily inputs)
canonicalCorrelatedResidualAsDegreeExpression
    {pseudoData = pseudoData}
    {firstVariationCovector = firstVariationCovector}
    {bondField = bondField}
    {plaquette = plaquette}
    inputs =
  let
    authority = Canonical.canonicalCorrelatedResidualAuthority inputs
    residualExact = Authority.canonicalCorrelatedResidualExact authority
    degreeExact = Degree.correlatedResidualIsJointDegreeExpression
      (canonicalFamily inputs)
  in
  DASHI.Physics.YangMills.BalabanP33CanonicalDegreeBridgeHelperExact.finish
    residualExact degreeExact

canonicalSubsetAuthorityFeedsDegreeBlocksLevel : ProofLevel
canonicalSubsetAuthorityFeedsDegreeBlocksLevel = machineChecked

-- The only remaining freedom is numerical/analytic enclosure of these literal
-- grouped functions over the selected region.  Their values and their KKT /
-- Möbius provenance are no longer independently supplied.
canonicalPhysicalDegreeBlockEnclosureLevel : ProofLevel
canonicalPhysicalDegreeBlockEnclosureLevel = conditional
