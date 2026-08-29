module DASHI.Physics.YangMills.BalabanCanonicalGreenStateNormReductionExact where

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
-- Combine the canonical degree-state preimages with the rank-independent KKT
-- constraint-image energy contraction.  For each source/defect degree d,
--
--   E_s(d) = <s_d,K+ s_d> <= ||g_d||^2,
--   E_d(d) = <delta_d,K+ delta_d> <= ||w_d||^2.
--
-- The existing PSD/polarization theorem therefore yields every signed Green
-- block from physical state norms alone:
--
--   -1/2 (||g_i||^2 + ||w_j||^2) <= G_ij.
--
-- This removes the global rowMass(K+) frontier entirely and remains valid
-- across background-dependent stabilizer/rank strata.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact as Diagonal
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseConstraintImageEnergyContractionExact as ImageEnergy
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact as Preimage
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

pseudoinverseEnergyRespectsPointwise :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    {left right : Multiplier → ℚ} →
  (∀ row → left row ≡ right row) →
  Positive.pseudoinverseEnergy pseudoData left
  ≡ Positive.pseudoinverseEnergy pseudoData right
pseudoinverseEnergyRespectsPointwise {Multiplier}
    pseudoData {left} {right} pointwise =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    pseudoCong : ∀ row →
      Pseudo.pseudoApply pseudoData left row
      ≡ Pseudo.pseudoApply pseudoData right row
    pseudoCong = Rect.applyRectangularVectorCong
      carrier (Pseudo.gramPseudoinverse pseudoData) pointwise
  in
  trans
    (Rect.finiteDotLeftPointwiseCong carrier pointwise)
    (Rect.finiteDotRightPointwiseCong carrier pseudoCong)

sourceStateNormSq :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → ℚ
sourceStateNormSq inputs degree =
  Rect.finiteNormSq KKT.physicalStateCarrier
    (Preimage.sourceDegreeState inputs degree)

defectStateNormSq :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → ℚ
defectStateNormSq inputs degree =
  Rect.finiteNormSq KKT.physicalStateCarrier
    (Preimage.defectDegreeState inputs degree)

sourceDegreeEnergyBelowStateNorm :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree →
  Diagonal.sourceDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) degree
  ≤ sourceStateNormSq inputs degree
sourceDegreeEnergyBelowStateNorm {pseudoData = pseudoData} inputs degree =
  let
    state = Preimage.sourceDegreeState inputs degree
    vector = GreenDegree.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree
    toImage : ∀ row →
      vector row ≡ Pseudo.constraintApply pseudoData state row
    toImage row = sym (Preimage.sourceDegreeStateConstraintExact inputs degree row)
    sameEnergy :
      Positive.pseudoinverseEnergy pseudoData vector
      ≡ Positive.pseudoinverseEnergy pseudoData
          (Pseudo.constraintApply pseudoData state)
    sameEnergy = pseudoinverseEnergyRespectsPointwise pseudoData toImage
  in
  subst
    (λ lower → lower ≤ sourceStateNormSq inputs degree)
    (sym sameEnergy)
    (ImageEnergy.constraintImagePseudoinverseEnergyBelowStateNormSq
      pseudoData state)

defectDegreeEnergyBelowStateNorm :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    degree →
  Diagonal.defectDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) degree
  ≤ defectStateNormSq inputs degree
defectDegreeEnergyBelowStateNorm {pseudoData = pseudoData} inputs degree =
  let
    state = Preimage.defectDegreeState inputs degree
    vector = GreenDegree.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree
    toImage : ∀ row →
      vector row ≡ Pseudo.constraintApply pseudoData state row
    toImage row = sym (Preimage.defectDegreeStateConstraintExact inputs degree row)
    sameEnergy :
      Positive.pseudoinverseEnergy pseudoData vector
      ≡ Positive.pseudoinverseEnergy pseudoData
          (Pseudo.constraintApply pseudoData state)
    sameEnergy = pseudoinverseEnergyRespectsPointwise pseudoData toImage
  in
  subst
    (λ lower → lower ≤ defectStateNormSq inputs degree)
    (sym sameEnergy)
    (ImageEnergy.constraintImagePseudoinverseEnergyBelowStateNormSq
      pseudoData state)

greenLowerFromStateNorms :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette} →
  Canonical.CanonicalSubsetCorrelatedAuthorityInputs
    {Multiplier} pseudoData firstVariationCovector bondField plaquette →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
greenLowerFromStateNorms inputs left right =
  - ((+ 1 / 2) *
      (sourceStateNormSq inputs left + defectStateNormSq inputs right))

greenLowerFromStateNormsSound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette)
    left right →
  greenLowerFromStateNorms inputs left right
  ≤ GreenDegree.greenDegreePairing
      (Canonical.canonicalConstraintAtoms inputs) left right
greenLowerFromStateNormsSound inputs left right =
  let
    sourceEnergy = Diagonal.sourceDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) left
    defectEnergy = Diagonal.defectDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) right
    sourceNorm = sourceStateNormSq inputs left
    defectNorm = defectStateNormSq inputs right
    sumBound : sourceEnergy + defectEnergy ≤ sourceNorm + defectNorm
    sumBound = ℚP.+-mono-≤
      (sourceDegreeEnergyBelowStateNorm inputs left)
      (defectDegreeEnergyBelowStateNorm inputs right)
    negated : - (sourceNorm + defectNorm) ≤ - (sourceEnergy + defectEnergy)
    negated = ℚP.neg-antimono-≤ sumBound
    scaled = Norm.scaleNonnegative
      (+ 1 / 2) (ℚP.nonNegative⁻¹ (+ 1 / 2)) negated
    normalized :
      greenLowerFromStateNorms inputs left right
      ≤ - ((+ 1 / 2) * (sourceEnergy + defectEnergy))
    normalized = subst
      (λ lower → lower ≤ - ((+ 1 / 2) * (sourceEnergy + defectEnergy)))
      (ℚRing.solve-∀ sourceNorm defectNorm)
      (subst
        (λ upper → (+ 1 / 2) * (- (sourceNorm + defectNorm)) ≤ upper)
        (ℚRing.solve-∀ sourceEnergy defectEnergy)
        scaled)
  in
  ℚP.≤-trans normalized
    (Diagonal.greenDegreeHalfEnergyLower
      (Canonical.canonicalConstraintAtoms inputs) left right)

canonicalGreenConstraintImageEnergyLevel : ProofLevel
canonicalGreenConstraintImageEnergyLevel = machineChecked

canonicalGreenStateNormReductionLevel : ProofLevel
canonicalGreenStateNormReductionLevel = machineChecked

-- Physical frontier after this theorem: charge-relative bounds on four source
-- state norms and four defect state norms.  No K+ row/entry/locality bound is a
-- G2 hypothesis any longer.
selectedRegionEightStateNormBoundsLevel : ProofLevel
selectedRegionEightStateNormBoundsLevel = conditional
