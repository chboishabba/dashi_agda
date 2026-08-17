module DASHI.Physics.YangMills.BalabanCanonicalGreenSchurNormReductionExact where

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
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- Issai Schur, classical matrix norm test (1911); no DOI applies.
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Specialize the Round60 PSD -> polarization -> Schur chain to the SAME
-- canonical subset/KKT/Moebius authority used by the Round58 G2 endpoint.
-- A physical selected-region proof now needs only
--
--   * one nonnegative absolute-row bound B for the literal K+;
--   * four source degree-vector norm-squared upper bounds;
--   * four defect degree-vector norm-squared upper bounds.
--
-- The theorem constructs a lower endpoint for every one of the sixteen signed
-- Green degree blocks.  No Green cell is independently estimated.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintDegreeBlocksExact as CanonicalBlocks
import DASHI.Physics.YangMills.BalabanSelectedConstraintGreenDegreeBilinearExact as GreenDegree
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeDiagonalReductionExact as Diagonal
import DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact as SchurEnergy
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record CanonicalGreenSchurNormData
    {Multiplier : Set}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette) : Set₁ where
  field
    rowBound : ℚ
    rowBoundNonnegative : 0ℚ ≤ rowBound
    rowsBounded : SchurEnergy.pseudoinverseRowBound pseudoData rowBound

    sourceNormUpper : Degree.MobiusDegree → ℚ
    defectNormUpper : Degree.MobiusDegree → ℚ

    sourceNormSound : ∀ degree →
      Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
        (GreenDegree.sourceDegreeVector
          (Canonical.canonicalConstraintAtoms inputs) degree)
      ≤ sourceNormUpper degree

    defectNormSound : ∀ degree →
      Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
        (GreenDegree.defectDegreeVector
          (Canonical.canonicalConstraintAtoms inputs) degree)
      ≤ defectNormUpper degree

open CanonicalGreenSchurNormData public

energyCoefficient : ℚ → ℚ
energyCoefficient bound = (+ 1 / 2) * ((+ 1 / 1) + bound * bound)

energyCoefficientNonnegative :
  ∀ bound → 0ℚ ≤ bound → 0ℚ ≤ energyCoefficient bound
energyCoefficientNonnegative bound boundNN =
  let
    boundSquareNN = FiniteL2.squareNonnegative bound
    onePlusSquareNN =
      FiniteL2.addNonnegative (ℚP.nonNegative⁻¹ (+ 1 / 1)) boundSquareNN
  in
  SchurEnergy.Schur.productNonnegative
    (+ 1 / 2) ((+ 1 / 1) + bound * bound)
    (ℚP.nonNegative⁻¹ (+ 1 / 2)) onePlusSquareNN

sourceEnergyUpper :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette} →
  CanonicalGreenSchurNormData inputs → Degree.MobiusDegree → ℚ
sourceEnergyUpper data degree =
  energyCoefficient (rowBound data) * sourceNormUpper data degree

defectEnergyUpper :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette} →
  CanonicalGreenSchurNormData inputs → Degree.MobiusDegree → ℚ
defectEnergyUpper data degree =
  energyCoefficient (rowBound data) * defectNormUpper data degree

sourceEnergySound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette}
    (data : CanonicalGreenSchurNormData inputs) degree →
  Diagonal.sourceDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) degree
  ≤ sourceEnergyUpper data degree
sourceEnergySound {pseudoData = pseudoData} {inputs = inputs} data degree =
  let
    vector = GreenDegree.sourceDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree
    operatorBound =
      SchurEnergy.pseudoinverseEnergySchurBound
        pseudoData vector (rowBound data)
        (rowBoundNonnegative data) (rowsBounded data)
    scaledNormBound =
      Norm.scaleNonnegative
        (energyCoefficient (rowBound data))
        (energyCoefficientNonnegative
          (rowBound data) (rowBoundNonnegative data))
        (sourceNormSound data degree)
  in
  ℚP.≤-trans operatorBound scaledNormBound

defectEnergySound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette}
    (data : CanonicalGreenSchurNormData inputs) degree →
  Diagonal.defectDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) degree
  ≤ defectEnergyUpper data degree
defectEnergySound {pseudoData = pseudoData} {inputs = inputs} data degree =
  let
    vector = GreenDegree.defectDegreeVector
      (Canonical.canonicalConstraintAtoms inputs) degree
    operatorBound =
      SchurEnergy.pseudoinverseEnergySchurBound
        pseudoData vector (rowBound data)
        (rowBoundNonnegative data) (rowsBounded data)
    scaledNormBound =
      Norm.scaleNonnegative
        (energyCoefficient (rowBound data))
        (energyCoefficientNonnegative
          (rowBound data) (rowBoundNonnegative data))
        (defectNormSound data degree)
  in
  ℚP.≤-trans operatorBound scaledNormBound

canonicalGreenIsBilinearPairing :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette)
    left right →
  CanonicalBlocks.canonicalGreenDegreeBlock inputs left right
  ≡ GreenDegree.greenDegreePairing
      (Canonical.canonicalConstraintAtoms inputs) left right
canonicalGreenIsBilinearPairing inputs left right =
  sym
    (GreenDegree.greenDegreePairingExact
      (Canonical.canonicalConstraintAtoms inputs) left right)

greenLowerFromSchurNorms :
  ∀ {Multiplier pseudoData firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      {Multiplier} pseudoData firstVariationCovector bondField plaquette} →
  CanonicalGreenSchurNormData inputs →
  Degree.MobiusDegree → Degree.MobiusDegree → ℚ
greenLowerFromSchurNorms data left right =
  - ((+ 1 / 2)
      * (sourceEnergyUpper data left + defectEnergyUpper data right))

greenLowerFromSchurNormsSound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    {firstVariationCovector bondField plaquette}
    {inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData firstVariationCovector bondField plaquette}
    (data : CanonicalGreenSchurNormData inputs)
    left right →
  greenLowerFromSchurNorms data left right
  ≤ CanonicalBlocks.canonicalGreenDegreeBlock inputs left right
greenLowerFromSchurNormsSound {inputs = inputs} data left right =
  let
    sourceActual = Diagonal.sourceDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) left
    defectActual = Diagonal.defectDegreeEnergy
      (Canonical.canonicalConstraintAtoms inputs) right
    sourceUpper = sourceEnergyUpper data left
    defectUpper = defectEnergyUpper data right

    energySumBelow :
      sourceActual + defectActual ≤ sourceUpper + defectUpper
    energySumBelow =
      ℚP.+-mono-≤
        (sourceEnergySound data left)
        (defectEnergySound data right)

    negated :
      - (sourceUpper + defectUpper)
      ≤ - (sourceActual + defectActual)
    negated = ℚP.neg-antimono-≤ energySumBelow

    scaled :
      (+ 1 / 2) * (- (sourceUpper + defectUpper))
      ≤ (+ 1 / 2) * (- (sourceActual + defectActual))
    scaled =
      Norm.scaleNonnegative
        (+ 1 / 2)
        (ℚP.nonNegative⁻¹ (+ 1 / 2)) negated

    normalized :
      - ((+ 1 / 2) * (sourceUpper + defectUpper))
      ≤ - ((+ 1 / 2) * (sourceActual + defectActual))
    normalized =
      subst
        (λ lower → lower ≤ - ((+ 1 / 2) * (sourceActual + defectActual)))
        (ℚRing.solve-∀ sourceUpper defectUpper)
        (subst
          (λ upper →
            (+ 1 / 2) * (- (sourceUpper + defectUpper)) ≤ upper)
          (ℚRing.solve-∀ sourceActual defectActual)
          scaled)

    diagonalLower =
      Diagonal.greenDegreeHalfEnergyLower
        (Canonical.canonicalConstraintAtoms inputs) left right

    toPairing = ℚP.≤-trans normalized diagonalLower
  in
  subst
    (λ upper → greenLowerFromSchurNorms data left right ≤ upper)
    (sym (canonicalGreenIsBilinearPairing inputs left right))
    toPairing

canonicalGreenSchurNormReductionLevel : ProofLevel
canonicalGreenSchurNormReductionLevel = machineChecked

-- The signed 4x4 Green table is no longer a physical numerical input.
-- Remaining selected-region Green data are exactly one K+ row bound plus
-- eight ordinary degree-vector norm-squared bounds.
selectedRegionCanonicalRowAndEightNormBoundsLevel : ProofLevel
selectedRegionCanonicalRowAndEightNormBoundsLevel = conditional
