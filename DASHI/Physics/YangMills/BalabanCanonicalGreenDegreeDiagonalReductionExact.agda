module DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact where

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
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- Remove the last possible same-object ambiguity between Round60's
-- pseudoinverse polarization theorem and Round58's CANONICAL G2 Green table.
-- The canonical correlated-residual family installs
-- `greenAtomPairContraction (canonicalConstraintAtoms inputs)` definitionally.
-- Consequently each canonical degree block is exactly the bilinear pairing
-- used by the Round60 diagonal-energy reduction.
--
-- Thus the 4x4 canonical table itself, not a parallel surrogate table, obeys
--
--   -(Q^S_d + Q^D_e) <= 2 G_de.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalDegree
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as DegreeGreen
import DASHI.Physics.YangMills.BalabanKKTGreenPolarizationLowerBoundExact as Polar
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree

canonicalGreenDegreeBlockIsPhysicalPairing :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    leftDegree rightDegree →
  CanonicalDegree.canonicalGreenDegreeBlock inputs leftDegree rightDegree
  ≡ DegreeGreen.greenDegreePairing
      (Canonical.canonicalConstraintAtoms inputs) leftDegree rightDegree
canonicalGreenDegreeBlockIsPhysicalPairing inputs leftDegree rightDegree =
  sym
    (DegreeGreen.greenDegreePairingExact
      (Canonical.canonicalConstraintAtoms inputs) leftDegree rightDegree)

canonicalSourceDegreeEnergy :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → ℚ
canonicalSourceDegreeEnergy inputs =
  Polar.sourceDegreeEnergy (Canonical.canonicalConstraintAtoms inputs)

canonicalDefectDegreeEnergy :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → ℚ
canonicalDefectDegreeEnergy inputs =
  Polar.defectDegreeEnergy (Canonical.canonicalConstraintAtoms inputs)

canonicalGreenDegreeLowerFromDiagonalEnergies :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    sourceDegree defectDegree →
  - (canonicalSourceDegreeEnergy inputs sourceDegree
      + canonicalDefectDegreeEnergy inputs defectDegree)
  ≤ CanonicalDegree.canonicalGreenDegreeBlock inputs sourceDegree defectDegree
      + CanonicalDegree.canonicalGreenDegreeBlock inputs sourceDegree defectDegree
canonicalGreenDegreeLowerFromDiagonalEnergies inputs sourceDegree defectDegree =
  let
    atoms = Canonical.canonicalConstraintAtoms inputs
    physicalPairing = DegreeGreen.greenDegreePairing atoms sourceDegree defectDegree
    canonicalBlock = CanonicalDegree.canonicalGreenDegreeBlock inputs sourceDegree defectDegree
    lower = Polar.degreeGreenLowerFromDiagonalEnergies atoms sourceDegree defectDegree
    identify = canonicalGreenDegreeBlockIsPhysicalPairing inputs sourceDegree defectDegree
  in
  subst
    (λ selected →
      - (canonicalSourceDegreeEnergy inputs sourceDegree
          + canonicalDefectDegreeEnergy inputs defectDegree)
      ≤ selected + selected)
    (sym identify)
    lower

canonicalGreenDegreeDiagonalReductionLevel : ProofLevel
canonicalGreenDegreeDiagonalReductionLevel = machineChecked
