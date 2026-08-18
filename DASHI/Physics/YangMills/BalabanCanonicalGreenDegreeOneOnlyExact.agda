module DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeOneOnlyExact where

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
-- DASHI CONTRIBUTION
--
-- The literal plaquette subset geometry kills source and defect Möbius degrees
-- 2,3,4 before the pseudoinverse is applied.  By bilinearity of the SAME KKT
-- Green pairing, any block with a higher source or defect degree is therefore
-- exactly zero.  The 4x4 canonical Green table has one possible survivor:
--
--                         G_11.
--
-- This exact zero theorem is stronger than the previous polarization lower
-- bounds and cuts the charge-relative Green penalty from
--
--   2 (sum_d s_d + sum_d t_d)
--
-- to the single-block cost
--
--   1/2 (s_1 + t_1).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact as Pairing
import DASHI.Physics.YangMills.BalabanCanonicalGreenHigherMobiusDegreeVanishExact as Vanish

------------------------------------------------------------------------
-- Proof-relevant classification of the higher degrees.
------------------------------------------------------------------------

data HigherDegree : Degree.MobiusDegree → Set where
  higher2 : HigherDegree Degree.degree2
  higher3 : HigherDegree Degree.degree3
  higher4 : HigherDegree Degree.degree4

sourceHigherVectorZero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    {degree} → HigherDegree degree →
  ∀ row →
  GreenDegree.sourceDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) degree row ≡ 0ℚ
sourceHigherVectorZero inputs higher2 = Vanish.sourceDegreeVector2Zero inputs
sourceHigherVectorZero inputs higher3 = Vanish.sourceDegreeVector3Zero inputs
sourceHigherVectorZero inputs higher4 = Vanish.sourceDegreeVector4Zero inputs

defectHigherVectorZero :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    {degree} → HigherDegree degree →
  ∀ row →
  GreenDegree.defectDegreeVector
    (Canonical.canonicalConstraintAtoms inputs) degree row ≡ 0ℚ
defectHigherVectorZero inputs higher2 = Vanish.defectDegreeVector2Zero inputs
defectHigherVectorZero inputs higher3 = Vanish.defectDegreeVector3Zero inputs
defectHigherVectorZero inputs higher4 = Vanish.defectDegreeVector4Zero inputs

------------------------------------------------------------------------
-- Exact zero blocks.
------------------------------------------------------------------------

canonicalGreenZeroFromHigherSource :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    {left} → HigherDegree left → ∀ right →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs left right ≡ 0ℚ
canonicalGreenZeroFromHigherSource
    {pseudoData = pseudoData} inputs higher right =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    atoms = Canonical.canonicalConstraintAtoms inputs
    source = GreenDegree.sourceDegreeVector atoms _
    transported = Pseudo.pseudoApply pseudoData
      (GreenDegree.defectDegreeVector atoms right)
  in
  trans
    (Pairing.canonicalGreenIsBilinearPairing inputs _ right)
    (trans
      (Rect.finiteDotLeftPointwiseCong carrier
        (sourceHigherVectorZero inputs higher))
      (Rect.finiteDotZeroLeft carrier transported))

canonicalGreenZeroFromHigherDefect :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    left {right} → HigherDegree right →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs left right ≡ 0ℚ
canonicalGreenZeroFromHigherDefect
    {pseudoData = pseudoData} inputs left higher =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    atoms = Canonical.canonicalConstraintAtoms inputs
    defect = GreenDegree.defectDegreeVector atoms _
    pseudoZero : ∀ row →
      Pseudo.pseudoApply pseudoData defect row ≡ 0ℚ
    pseudoZero row =
      trans
        (Rect.applyRectangularVectorCong
          carrier (Pseudo.gramPseudoinverse pseudoData)
          (defectHigherVectorZero inputs higher) row)
        (Rect.applyRectangularZero
          carrier (Pseudo.gramPseudoinverse pseudoData) row)
  in
  trans
    (Pairing.canonicalGreenIsBilinearPairing inputs left _)
    (trans
      (Rect.finiteDotRightPointwiseCong carrier pseudoZero)
      (Rect.finiteDotZeroRight carrier
        (GreenDegree.sourceDegreeVector atoms left)))

-- Explicit named eliminators used by the degree-one G2 compiler.
g12Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree2 ≡ 0ℚ
g12Zero inputs = canonicalGreenZeroFromHigherDefect inputs Degree.degree1 higher2

g13Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree3 ≡ 0ℚ
g13Zero inputs = canonicalGreenZeroFromHigherDefect inputs Degree.degree1 higher3

g14Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree1 Degree.degree4 ≡ 0ℚ
g14Zero inputs = canonicalGreenZeroFromHigherDefect inputs Degree.degree1 higher4

g21Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree2 Degree.degree1 ≡ 0ℚ
g21Zero inputs = canonicalGreenZeroFromHigherSource inputs higher2 Degree.degree1

g31Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree3 Degree.degree1 ≡ 0ℚ
g31Zero inputs = canonicalGreenZeroFromHigherSource inputs higher3 Degree.degree1

g41Zero : ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
  (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette) →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs Degree.degree4 Degree.degree1 ≡ 0ℚ
g41Zero inputs = canonicalGreenZeroFromHigherSource inputs higher4 Degree.degree1

canonicalGreenDegreeOneOnlyLevel : ProofLevel
canonicalGreenDegreeOneOnlyLevel = machineChecked
