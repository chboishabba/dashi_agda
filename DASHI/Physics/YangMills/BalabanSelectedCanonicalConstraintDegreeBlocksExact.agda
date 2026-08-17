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
-- Weld the canonical selected residual authority to the exact 4 raw + 16 Green
-- Möbius-degree decomposition.  The grouped quantities consumed by the
-- Round58 interval producer are therefore the degree sums of the SAME literal
-- subset/KKT/Möbius authority, not independently supplied surrogates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _-_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualAuthorityExact as Authority
import DASHI.Physics.YangMills.BalabanSelectedConstraintAtomGreenExpansionExact as GreenExpansion
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
  Ownership.CorrelatedResidualFamily
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

canonicalRawLocalizationIsDegreeTotal :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  Canonical.rawLocalization inputs
  ≡ Degree.rawDegreeTotal (canonicalFamily inputs)
canonicalRawLocalizationIsDegreeTotal inputs =
  trans
    (sym (Canonical.rawLocalizationReconstruct inputs))
    (Degree.rawTotalIsDegreeTotal (canonicalFamily inputs))

canonicalMultiplierGreenPairingIsDegreeTotal :
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
  ≡ Degree.greenDegreeTotal (canonicalFamily inputs)
canonicalMultiplierGreenPairingIsDegreeTotal inputs =
  trans
    (GreenExpansion.constraintAtomGreenExpansionExact
      (Canonical.canonicalConstraintAtoms inputs))
    (Degree.greenTotalIsDegreeTotal (canonicalFamily inputs))

canonicalCorrelatedResidualAsLiteralRawMinusGroupedGreen :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector : KKT.StateVector}
    {bondField : Physical.PhysicalSU2BondField4}
    {plaquette : Plaquette.Plaquette4}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Ownership.correlatedResidualTotal (canonicalFamily inputs)
  ≡ Canonical.rawLocalization inputs
      - Degree.greenDegreeTotal (canonicalFamily inputs)
canonicalCorrelatedResidualAsLiteralRawMinusGroupedGreen
    {pseudoData = pseudoData}
    {firstVariationCovector = firstVariationCovector}
    {bondField = bondField}
    {plaquette = plaquette}
    inputs =
  trans
    (Authority.canonicalCorrelatedResidualExact
      (Canonical.canonicalCorrelatedResidualAuthority inputs))
    (cong
      (Canonical.rawLocalization inputs -_)
      (canonicalMultiplierGreenPairingIsDegreeTotal inputs))

canonicalCorrelatedResidualAsTwentyDegreeBlocks :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  Ownership.correlatedResidualTotal (canonicalFamily inputs)
  ≡ Degree.rawDegreeTotal (canonicalFamily inputs)
      - Degree.greenDegreeTotal (canonicalFamily inputs)
canonicalCorrelatedResidualAsTwentyDegreeBlocks inputs =
  Degree.correlatedResidualIsJointDegreeExpression (canonicalFamily inputs)

canonicalSubsetAuthorityFeedsDegreeBlocksLevel : ProofLevel
canonicalSubsetAuthorityFeedsDegreeBlocksLevel = machineChecked

canonicalGreenPairingDegreeIdentificationLevel : ProofLevel
canonicalGreenPairingDegreeIdentificationLevel = machineChecked

-- Remaining freedom is now only numerical/analytic enclosure of these literal
-- grouped functions over the selected region.  Their values and KKT/Möbius
-- provenance are not independent inputs.
canonicalPhysicalDegreeBlockEnclosureLevel : ProofLevel
canonicalPhysicalDegreeBlockEnclosureLevel = conditional
