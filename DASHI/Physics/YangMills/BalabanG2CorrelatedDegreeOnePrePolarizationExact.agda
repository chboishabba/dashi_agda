module DASHI.Physics.YangMills.BalabanG2CorrelatedDegreeOnePrePolarizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
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
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- DASHI CONTRIBUTION
--
-- The literal plaquette subset theorem kills every Green degree block except
-- G_11.  The exact defect calculation then shows that separately polarizing
-- source and defect norms cannot fit the selected singleton headroom: the
-- defect term alone costs 1/6, while the complete target is only
-- 55/18874368.  Therefore the live object must retain the signed cancellation
-- BEFORE polarization.
--
-- This file makes that corrected target exact on the SAME canonical family:
--
--   R_corr = (R_1 - G_11) + (R_2 + R_3 + R_4).
--
-- No absolute value, source-norm majorant, pseudoinverse row bound, or LBB
-- constant is inserted.  Future physical interval work can now enclose the
-- signed degree-one core directly and only then add genuinely surviving higher
-- raw degrees.  The final theorem below wires precisely that signed enclosure
-- into the already-selected singleton coefficient.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanP33PhysicalWilsonSignedGlobalExact as Wilson
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact as Selector
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeOneOnlyExact as DegreeOne

canonicalGreenDegreeTotalIsG11 :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  Degree.greenDegreeTotal (Blocks.canonicalFamily inputs)
  ≡ Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1
canonicalGreenDegreeTotalIsG11 inputs
  rewrite DegreeOne.g12Zero inputs
        | DegreeOne.g13Zero inputs
        | DegreeOne.g14Zero inputs
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher2 Degree.degree1
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher2 Degree.degree2
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher2 Degree.degree3
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher2 Degree.degree4
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher3 Degree.degree1
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher3 Degree.degree2
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher3 Degree.degree3
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher3 Degree.degree4
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher4 Degree.degree1
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher4 Degree.degree2
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher4 Degree.degree3
        | DegreeOne.canonicalGreenZeroFromHigherSource
            inputs DegreeOne.higher4 Degree.degree4 =
  ℚRing.solve-∀
    (Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1)

signedDegreeOneCore :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette → ℚ
signedDegreeOneCore inputs =
  Blocks.canonicalRawDegreeBlock inputs Degree.degree1
  - Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1

higherRawCore :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette → ℚ
higherRawCore inputs =
  Blocks.canonicalRawDegreeBlock inputs Degree.degree2
  + Blocks.canonicalRawDegreeBlock inputs Degree.degree3
  + Blocks.canonicalRawDegreeBlock inputs Degree.degree4

canonicalCorrelatedResidualIsSignedDegreeOnePlusHigherRaw :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs)
  ≡ signedDegreeOneCore inputs + higherRawCore inputs
canonicalCorrelatedResidualIsSignedDegreeOnePlusHigherRaw inputs =
  trans
    (Blocks.canonicalCorrelatedResidualAsTwentyDegreeBlocks inputs)
    (trans
      (cong
        (λ green → Degree.rawDegreeTotal (Blocks.canonicalFamily inputs) - green)
        (canonicalGreenDegreeTotalIsG11 inputs))
      (ℚRing.solve-∀
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree1)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree2)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree3)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree4)
        (Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1)))

canonicalCorrelatedResidualUpperFromSignedCore :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    (upper : ℚ) →
  signedDegreeOneCore inputs + higherRawCore inputs ≤ upper →
  Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs) ≤ upper
canonicalCorrelatedResidualUpperFromSignedCore inputs upper bound =
  subst
    (λ value → value ≤ upper)
    (sym (canonicalCorrelatedResidualIsSignedDegreeOnePlusHigherRaw inputs))
    bound

selectedCorrelatedResidualUpperFromSignedPrePolarization :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  signedDegreeOneCore inputs + higherRawCore inputs
    ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette →
  Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs)
    ≤ Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette
selectedCorrelatedResidualUpperFromSignedPrePolarization
    {bondField = bondField} {plaquette = plaquette} inputs =
  canonicalCorrelatedResidualUpperFromSignedCore inputs
    (Selector.remainingSingletonCoefficient
      * Wilson.plaquetteCrossCharge bondField plaquette)

canonicalGreenTotalDegreeOneOnlyLevel : ProofLevel
canonicalGreenTotalDegreeOneOnlyLevel = machineChecked

correlatedDegreeOnePrePolarizationIdentityLevel : ProofLevel
correlatedDegreeOnePrePolarizationIdentityLevel = machineChecked

selectedSignedPrePolarizationToSingletonTargetLevel : ProofLevel
selectedSignedPrePolarizationToSingletonTargetLevel = machineChecked

-- This is the corrected live G2 physical producer.  Separate nonnegative
-- source/defect norm majorants are provably too lossy on the selected target.
selectedRegionSignedDegreeOnePlusHigherRawEnclosureLevel : ProofLevel
selectedRegionSignedDegreeOnePlusHigherRawEnclosureLevel = conditional
