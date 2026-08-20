module DASHI.Physics.YangMills.BalabanKKTPseudoinverseSchurEnergyBoundExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Issai Schur, classical matrix norm test (1911); no DOI applies.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Roger Penrose,
-- "A Generalized Inverse for Matrices", Proc. Cambridge Philosophical
-- Society 51 (1955), 406--413. DOI: 10.1017/S0305004100030401.
--
-- DASHI CONTRIBUTION
--
-- For the symmetric KKT pseudoinverse K+, one common absolute-row bound B
-- yields the square-root-free Schur estimate
--
--   ||K+ v||^2 <= B^2 ||v||^2.
--
-- Positivity of the ordinary square ||v-K+v||^2 then gives
--
--   2 <v,K+v> <= ||v||^2 + ||K+v||^2,
--
-- hence
--
--   <v,K+v> <= (1/2)(1+B^2)||v||^2.
--
-- Thus the eight Round60 diagonal Green-energy bounds reduce to one common
-- pseudoinverse row-mass bound plus eight ordinary vector norm-squared bounds.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanKKTGramPseudoinversePositiveExact as Positive

pseudoinverseRowBound :
  ∀ {Multiplier} →
  Pseudo.FiniteKKTPseudoinverseData Multiplier → ℚ → Set
pseudoinverseRowBound pseudoData bound =
  ∀ row →
    Schur.absoluteRowMass
      (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
      (Pseudo.gramPseudoinverse pseudoData) row
    ≤ bound

pseudoinverseImageNormSchurBound :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector bound →
  0ℚ ≤ bound →
  pseudoinverseRowBound pseudoData bound →
  Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
      (Pseudo.pseudoApply pseudoData vector)
  ≤ (bound * bound)
      * Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData) vector
pseudoinverseImageNormSchurBound pseudoData vector bound
    boundNonnegative rowsBounded =
  Schur.finiteSymmetricSchurSquared
    (Matrix.coordinates (Pseudo.multiplierCarrier pseudoData))
    (Pseudo.gramPseudoinverse pseudoData)
    vector bound
    boundNonnegative
    (Pseudo.gramPseudoinverseSymmetric pseudoData)
    rowsBounded

normDifferenceExpansion :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
      (Rect.vectorSubtract vector (Pseudo.pseudoApply pseudoData vector))
  ≡ Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData) vector
      + Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
          (Pseudo.pseudoApply pseudoData vector)
      - (Positive.pseudoinverseEnergy pseudoData vector
        + Positive.pseudoinverseEnergy pseudoData vector)
normDifferenceExpansion pseudoData vector =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    image = Pseudo.pseudoApply pseudoData vector
    energy = Positive.pseudoinverseEnergy pseudoData vector
    vectorNorm = Rect.finiteNormSq carrier vector
    imageNorm = Rect.finiteNormSq carrier image

    expanded :
      Rect.finiteDot carrier
        (Rect.vectorSubtract vector image)
        (Rect.vectorSubtract vector image)
      ≡ (Rect.finiteDot carrier vector vector
          - Rect.finiteDot carrier vector image)
        - (Rect.finiteDot carrier image vector
          - Rect.finiteDot carrier image image)
    expanded =
      trans
        (Rect.finiteDotSubtractLeft carrier vector image
          (Rect.vectorSubtract vector image))
        (cong₂ _-_
          (Rect.finiteDotSubtractRight carrier vector vector image)
          (Rect.finiteDotSubtractRight carrier image vector image))

    crossSymmetric :
      Rect.finiteDot carrier image vector ≡ energy
    crossSymmetric = Rect.finiteDotSymmetric carrier image vector
  in
  trans expanded
    (trans
      (cong
        (λ selected →
          (vectorNorm - energy) - (selected - imageNorm))
        crossSymmetric)
      (ℚRing.solve-∀ vectorNorm imageNorm energy))

energyDoubleBelowNormSum :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector →
  Positive.pseudoinverseEnergy pseudoData vector
    + Positive.pseudoinverseEnergy pseudoData vector
  ≤ Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData) vector
    + Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData)
        (Pseudo.pseudoApply pseudoData vector)
energyDoubleBelowNormSum pseudoData vector =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    image = Pseudo.pseudoApply pseudoData vector
    energy = Positive.pseudoinverseEnergy pseudoData vector
    vectorNorm = Rect.finiteNormSq carrier vector
    imageNorm = Rect.finiteNormSq carrier image

    differenceNonnegative :
      0ℚ ≤ (vectorNorm + imageNorm) - (energy + energy)
    differenceNonnegative =
      subst
        (λ selected → 0ℚ ≤ selected)
        (normDifferenceExpansion pseudoData vector)
        (Rect.finiteNormSqNonnegative carrier
          (Rect.vectorSubtract vector image))
  in
  Norm.nonnegativeDifferenceImpliesBelow differenceNonnegative

pseudoinverseEnergySchurBound :
  ∀ {Multiplier}
    (pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier)
    vector bound →
  0ℚ ≤ bound →
  pseudoinverseRowBound pseudoData bound →
  Positive.pseudoinverseEnergy pseudoData vector
  ≤ (+ 1 / 2) * ((+ 1 / 1) + bound * bound)
      * Rect.finiteNormSq (Pseudo.multiplierCarrier pseudoData) vector
pseudoinverseEnergySchurBound pseudoData vector bound
    boundNonnegative rowsBounded =
  let
    carrier = Pseudo.multiplierCarrier pseudoData
    image = Pseudo.pseudoApply pseudoData vector
    energy = Positive.pseudoinverseEnergy pseudoData vector
    vectorNorm = Rect.finiteNormSq carrier vector
    imageNorm = Rect.finiteNormSq carrier image

    imageBound : imageNorm ≤ (bound * bound) * vectorNorm
    imageBound =
      pseudoinverseImageNormSchurBound
        pseudoData vector bound boundNonnegative rowsBounded

    sumBound :
      vectorNorm + imageNorm
      ≤ vectorNorm + (bound * bound) * vectorNorm
    sumBound = ℚP.+-monoˡ-≤ vectorNorm imageBound

    doubleBound :
      energy + energy
      ≤ vectorNorm + (bound * bound) * vectorNorm
    doubleBound =
      ℚP.≤-trans (energyDoubleBelowNormSum pseudoData vector) sumBound

    scaled =
      Norm.scaleNonnegative
        (+ 1 / 2)
        (ℚP.nonNegative⁻¹ (+ 1 / 2))
        doubleBound
  in
  subst
    (λ lower → lower
      ≤ (+ 1 / 2) * ((+ 1 / 1) + bound * bound) * vectorNorm)
    (ℚRing.solve-∀ energy)
    (subst
      (λ upper →
        (+ 1 / 2) * (energy + energy) ≤ upper)
      (ℚRing.solve-∀ bound vectorNorm)
      scaled)

kktPseudoinverseSchurEnergyBoundLevel : ProofLevel
kktPseudoinverseSchurEnergyBoundLevel = machineChecked
