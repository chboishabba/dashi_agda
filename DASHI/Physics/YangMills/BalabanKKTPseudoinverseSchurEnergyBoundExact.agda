module DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911).  No DOI applies to the
-- original result.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proceedings of the Cambridge
-- Philosophical Society 51 (1955), 406--413.
-- DOI: 10.1017/S0305004100030401.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- For the same symmetric K+ used by G2, a common absolute-row-mass bound B
-- gives the square-root-free Schur estimate
--
--   ||K+ v||^2 <= B^2 ||v||^2.
--
-- Together with 2<v,K+v> <= ||v||^2 + ||K+v||^2 this yields
--
--   <v,K+v> <= (1/2)(1+B^2)||v||^2.
--
-- The proof uses the actual implicit-endpoint API of
-- `nonnegativeDifferenceImpliesBelow`.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive

half : ℚ
half = + 1 / 2

twoCrossBelowSquares : ∀ left right →
  left * right + left * right
  ≤ FiniteL2.square left + FiniteL2.square right
twoCrossBelowSquares left right =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ selected → 0ℚ ≤ selected)
      (ℚRing.solve-∀ left right)
      (FiniteL2.squareNonnegative (left - right)))

pseudoEnergyDoubleBelowInputPlusOutputNorm :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  Positive.pseudoQuadratic pseudoData vector
    + Positive.pseudoQuadratic pseudoData vector
  ≤ Schur.vectorNormSq
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)) vector
    + Schur.vectorNormSq
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (Pseudo.pseudoApply pseudoData vector)
pseudoEnergyDoubleBelowInputPlusOutputNorm pseudoData vector =
  let
    indices = Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)
    pseudoVector = Pseudo.pseudoApply pseudoData vector

    pointwise : ∀ index →
      vector index * pseudoVector index + vector index * pseudoVector index
      ≤ FiniteL2.square (vector index) + FiniteL2.square (pseudoVector index)
    pointwise index = twoCrossBelowSquares (vector index) (pseudoVector index)

    summed = Schur.sumPointwiseBelow
      indices
      (λ index → vector index * pseudoVector index
        + vector index * pseudoVector index)
      (λ index → FiniteL2.square (vector index)
        + FiniteL2.square (pseudoVector index))
      pointwise

    leftSplit = Fubini.sumRationalAdd
      indices
      (λ index → vector index * pseudoVector index)
      (λ index → vector index * pseudoVector index)

    rightSplit = Fubini.sumRationalAdd
      indices
      (λ index → FiniteL2.square (vector index))
      (λ index → FiniteL2.square (pseudoVector index))
  in
  subst
    (λ left → left
      ≤ Schur.vectorNormSq indices vector + Schur.vectorNormSq indices pseudoVector)
    leftSplit
    (subst
      (λ right →
        Sums.sumRational indices
          (λ index → vector index * pseudoVector index
            + vector index * pseudoVector index)
        ≤ right)
      rightSplit summed)

record PseudoinverseSchurBound
    {Multiplier : Set}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier) : Set where
  field
    rowMassBound : ℚ
    rowMassBoundNonnegative : 0ℚ ≤ rowMassBound
    rowsBounded : ∀ row →
      Schur.absoluteRowMass
        (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
        (Pseudo.gramPseudoinverse pseudoData) row
      ≤ rowMassBound
open PseudoinverseSchurBound public

pseudoOutputNormBound :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (schur : PseudoinverseSchurBound pseudoData)
    vector →
  Schur.vectorNormSq
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (Pseudo.pseudoApply pseudoData vector)
  ≤ (rowMassBound schur * rowMassBound schur)
      * Schur.vectorNormSq
          (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)) vector
pseudoOutputNormBound {pseudoData = pseudoData} schur vector =
  Schur.finiteSymmetricSchurSquared
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (Pseudo.gramPseudoinverse pseudoData)
    vector
    (rowMassBound schur)
    (rowMassBoundNonnegative schur)
    (Pseudo.gramPseudoinverseSymmetric pseudoData)
    (rowsBounded schur)

pseudoEnergyUpperFromVectorNorm :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    (schur : PseudoinverseSchurBound pseudoData)
    vector vectorNormUpper →
  Schur.vectorNormSq
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)) vector
    ≤ vectorNormUpper →
  Positive.pseudoQuadratic pseudoData vector
  ≤ half * ((1ℚ + rowMassBound schur * rowMassBound schur) * vectorNormUpper)
pseudoEnergyUpperFromVectorNorm
    {pseudoData = pseudoData} schur vector vectorNormUpper normUpper =
  let
    indices = Matrix.coordinates (Pseudo.multiplierCarrier pseudoData)
    bound = rowMassBound schur
    q = Positive.pseudoQuadratic pseudoData vector
    inputNorm = Schur.vectorNormSq indices vector
    outputNorm = Schur.vectorNormSq indices (Pseudo.pseudoApply pseudoData vector)
    factor = 1ℚ + bound * bound

    outputBound : outputNorm ≤ (bound * bound) * inputNorm
    outputBound = pseudoOutputNormBound schur vector

    sumBound : inputNorm + outputNorm ≤ factor * inputNorm
    sumBound = ℚP.≤-trans
      (ℚP.+-mono-≤ ℚP.≤-refl outputBound)
      (subst
        (λ right → inputNorm + (bound * bound) * inputNorm ≤ right)
        (ℚRing.solve-∀ bound inputNorm)
        ℚP.≤-refl)

    doubledEnergy : q + q ≤ factor * inputNorm
    doubledEnergy = ℚP.≤-trans
      (pseudoEnergyDoubleBelowInputPlusOutputNorm pseudoData vector)
      sumBound

    factorNonnegative : 0ℚ ≤ factor
    factorNonnegative =
      FiniteL2.addNonnegative
        (ℚP.nonNegative⁻¹ 1ℚ)
        (FiniteL2.squareNonnegative bound)

    scaledNorm : factor * inputNorm ≤ factor * vectorNormUpper
    scaledNorm = Norm.scaleNonnegative factor factorNonnegative normUpper

    doubledToUpper : q + q ≤ factor * vectorNormUpper
    doubledToUpper = ℚP.≤-trans doubledEnergy scaledNorm

    halfScaled = Norm.scaleNonnegative half
      (ℚP.nonNegative⁻¹ half) doubledToUpper
  in
  subst
    (λ left → left ≤ half * (factor * vectorNormUpper))
    (ℚRing.solve-∀ q)
    halfScaled

kktPseudoinverseSchurEnergyBoundLevel : ProofLevel
kktPseudoinverseSchurEnergyBoundLevel = machineChecked

selectedRegionPseudoinverseRowMassAndEightVectorNormsLevel : ProofLevel
selectedRegionPseudoinverseRowMassAndEightVectorNormsLevel = conditional
