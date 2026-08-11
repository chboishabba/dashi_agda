module DASHI.Physics.YangMills.BalabanSelectedConstraintDerivativeVariationBudgetExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309. DOI: 10.1007/BF01229381.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- DASHI CONTRIBUTION
--
-- Turn the exact 1024/29 normal-correction estimate into the next concrete
-- nonlinear target.  If the variation of the selected nonlinear constraint
-- derivative obeys the squared-operator estimate
--
--       ||(D C(U)-D C(A)) v||^2
--         <= (29/2048) ||v||^2,
--
-- then composing it with the exact reduced normal correction N_A gives
--
--       ||(D C(U)-D C(A)) N_A y||^2
--         <= (1/2) ||y||^2.
--
-- Thus 29/2048 is a literal sufficient derivative-variation target for a
-- half-contractive Newton normal correction in squared norm.  The theorem is
-- not an abstract IFT receipt: the inverse constant is the selected 29/1024
-- floor already proved on the same finite operator, and only the genuinely
-- nonlinear derivative-variation estimate remains physical work.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)
open import Relation.Nullary.Decidable.Core using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact as Matrix
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as StateCarrier
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintFiniteKKTExact as RawKKT
import DASHI.Physics.YangMills.BalabanSelectedPaddedReducedNormalInverseExact as ReducedInverse
import DASHI.Physics.YangMills.BalabanSelectedReducedNormalCorrectionBoundExact as Bound

StateVector : Set
StateVector = StateCarrier.StateVector

MultiplierVector : Set
MultiplierVector = ReducedInverse.RawMultiplier

derivativeVariationSquaredCoefficient : ℚ
derivativeVariationSquaredCoefficient = + 29 / 2048

halfContractionSquaredCoefficient : ℚ
halfContractionSquaredCoefficient = + 1 / 2

derivativeVariationSquaredCoefficientNonnegative :
  0ℚ ≤ derivativeVariationSquaredCoefficient
derivativeVariationSquaredCoefficientNonnegative =
  toWitness {a? = 0ℚ ≤? derivativeVariationSquaredCoefficient} _

derivativeVariationBudgetExact :
  derivativeVariationSquaredCoefficient * Bound.selectedFloorReciprocal
  ≡ halfContractionSquaredCoefficient
derivativeVariationBudgetExact = ℚRing.solve []

selectedNormalCorrectionFromSource :
  ∀ background →
  Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background) →
  MultiplierVector → StateVector
selectedNormalCorrectionFromSource background certificate source =
  RawKKT.selectedCombinedConstraintTransposeApply background
    (ReducedInverse.selectedReducedNormalInverseApply
      background certificate source)

selectedNormalCorrectionFromSourceBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background)) →
  source → ReducedInverse.ReducedSource source →
  Rect.finiteNormSq StateCarrier.physicalStateCarrier
      (selectedNormalCorrectionFromSource background certificate source)
  ≤ Bound.selectedFloorReciprocal * Bound.rawMultiplierNormSq source
selectedNormalCorrectionFromSourceBound = Bound.selectedReducedNormalCorrectionBound

selectedDerivativeVariationComposedWithNormalUpper :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  (certificate : Matrix.RationalMatrixInverseCertificate
    Rows.selectedCombinedConstraintRowCarrier
    (ReducedInverse.selectedPaddedReducedNormalMatrix background)) →
  (variation : StateVector → MultiplierVector) →
  (∀ vector →
    Bound.rawMultiplierNormSq (variation vector)
    ≤ derivativeVariationSquaredCoefficient
      * Rect.finiteNormSq StateCarrier.physicalStateCarrier vector) →
  source → ReducedInverse.ReducedSource source →
  Bound.rawMultiplierNormSq
      (variation
        (selectedNormalCorrectionFromSource background certificate source))
  ≤ halfContractionSquaredCoefficient * Bound.rawMultiplierNormSq source
selectedDerivativeVariationComposedWithNormalUpper
    background radius certificate variation variationUpper source sourceReduced =
  let
    correction = selectedNormalCorrectionFromSource background certificate source

    first = variationUpper correction

    correctionBound = selectedNormalCorrectionFromSourceBound
      background radius certificate source sourceReduced

    scaled = Norm.scaleNonnegative derivativeVariationSquaredCoefficient
      derivativeVariationSquaredCoefficientNonnegative correctionBound

    composed :
      Bound.rawMultiplierNormSq (variation correction)
      ≤ derivativeVariationSquaredCoefficient
          * (Bound.selectedFloorReciprocal * Bound.rawMultiplierNormSq source)
    composed = ℚP.≤-trans first scaled
  in
  subst
    (λ upper → Bound.rawMultiplierNormSq (variation correction) ≤ upper)
    (ℚRing.solve-∀ (Bound.rawMultiplierNormSq source) :
      derivativeVariationSquaredCoefficient
        * (Bound.selectedFloorReciprocal * Bound.rawMultiplierNormSq source)
      ≡ halfContractionSquaredCoefficient * Bound.rawMultiplierNormSq source)
    composed

selectedDerivativeVariationBudgetLevel : ProofLevel
selectedDerivativeVariationBudgetLevel = machineChecked

selectedDerivativeVariationPhysicalEstimateLevel : ProofLevel
selectedDerivativeVariationPhysicalEstimateLevel = conditional
