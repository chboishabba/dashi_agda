module DASHI.Physics.YangMills.BalabanCanonicalCorrelatedDegreeOneBeforePolarizationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368. DOI: 10.1007/BF00531932.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- The literal plaquette subset geometry has already proved that every source
-- and defect Möbius degree above one vanishes before the KKT pseudoinverse.
-- Hence fifteen of the sixteen Green blocks vanish exactly.  This file now
-- pushes that cancellation all the way through the canonical correlated
-- residual BEFORE any polarization or absolute-value bound:
--
--   R_corr
--     = (R1 + R2 + R3 + R4) - G11
--     = (R1 - G11) + R2 + R3 + R4.
--
-- This is the correct post-falsifier G2 object.  The degree-one term must be
-- enclosed JOINTLY as raw_1-G_11; separately majorizing ||g_1|| and ||w_1||
-- provably loses more than fifty-seven thousand singleton budgets.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as Blocks
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeOneOnlyExact as DegreeOne

canonicalGreenDegreeTotalIsG11 :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector : KKT.StateVector}
    {bondField : Physical.PhysicalSU2BondField4}
    {plaquette : Plaquette.Plaquette4}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Degree.greenDegreeTotal (Blocks.canonicalFamily inputs)
  ≡ Blocks.canonicalGreenDegreeBlock
      inputs Degree.degree1 Degree.degree1
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

canonicalRawDegreeTotalExpanded :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  Degree.rawDegreeTotal (Blocks.canonicalFamily inputs)
  ≡ Blocks.canonicalRawDegreeBlock inputs Degree.degree1
    + Blocks.canonicalRawDegreeBlock inputs Degree.degree2
    + Blocks.canonicalRawDegreeBlock inputs Degree.degree3
    + Blocks.canonicalRawDegreeBlock inputs Degree.degree4
canonicalRawDegreeTotalExpanded inputs = ℚRing.solve-∀
  (Blocks.canonicalRawDegreeBlock inputs Degree.degree1)
  (Blocks.canonicalRawDegreeBlock inputs Degree.degree2)
  (Blocks.canonicalRawDegreeBlock inputs Degree.degree3)
  (Blocks.canonicalRawDegreeBlock inputs Degree.degree4)

canonicalCorrelatedDegreeOne :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette → ℚ
canonicalCorrelatedDegreeOne inputs =
  Blocks.canonicalRawDegreeBlock inputs Degree.degree1
  - Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1

canonicalRawHigherDegreeTotal :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette → ℚ
canonicalRawHigherDegreeTotal inputs =
  Blocks.canonicalRawDegreeBlock inputs Degree.degree2
  + Blocks.canonicalRawDegreeBlock inputs Degree.degree3
  + Blocks.canonicalRawDegreeBlock inputs Degree.degree4

canonicalCorrelatedResidualDegreeOneBeforePolarization :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector : KKT.StateVector}
    {bondField : Physical.PhysicalSU2BondField4}
    {plaquette : Plaquette.Plaquette4}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) →
  Ownership.correlatedResidualTotal (Blocks.canonicalFamily inputs)
  ≡ canonicalCorrelatedDegreeOne inputs
    + canonicalRawHigherDegreeTotal inputs
canonicalCorrelatedResidualDegreeOneBeforePolarization inputs =
  trans
    (Blocks.canonicalCorrelatedResidualAsTwentyDegreeBlocks inputs)
    (trans
      (let
        rawExpanded = canonicalRawDegreeTotalExpanded inputs
        greenCollapsed = canonicalGreenDegreeTotalIsG11 inputs
      in
      Relation.Binary.PropositionalEquality.cong₂ _-_
        rawExpanded greenCollapsed)
      (ℚRing.solve-∀
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree1)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree2)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree3)
        (Blocks.canonicalRawDegreeBlock inputs Degree.degree4)
        (Blocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree1)))
  where
  import Relation.Binary.PropositionalEquality

canonicalCorrelatedDegreeOneReductionLevel : ProofLevel
canonicalCorrelatedDegreeOneReductionLevel = machineChecked

-- The live G2 numerical work is now exactly:
--   (i) a signed upper bound on canonicalCorrelatedDegreeOne;
--   (ii) an upper bound on canonicalRawHigherDegreeTotal;
--   (iii) one coefficient sum against 55/18874368.
selectedRegionCorrelatedD1AndRawHigherProducerLevel : ProofLevel
selectedRegionCorrelatedD1AndRawHigherProducerLevel = conditional
