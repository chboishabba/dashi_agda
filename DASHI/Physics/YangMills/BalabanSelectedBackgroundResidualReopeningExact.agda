module DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualReopeningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- J. M. Combes and L. Thomas,
-- "Asymptotic Behaviour of Eigenfunctions for Multiparticle Schrödinger
-- Operators", Communications in Mathematical Physics 34 (1973), 251--270.
-- DOI: 10.1007/BF01646473.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- DASHI CONTRIBUTION
--
-- Consume the literal selected residual estimates as reopening equations,
-- rather than defining an inverse by an infinite Neumann sum over Q.
--
-- Unweighted:
--
--   x + R_A x = y,  ||R_A x||_1 <= (1/10)||x||_1
--
-- implies
--
--   ||x||_1 <= (10/9)||y||_1.
--
-- With the already-constructed rational Combes--Thomas conjugation:
--
--   x + (D R_A D^-1)x = y,
--   ||(D R_A D^-1)x||_1 <= (1/6)||x||_1
--
-- implies
--
--   ||x||_1 <= (6/5)||y||_1.
--
-- The residual operators are proved linear under finite subtraction.  Combining
-- this with the complete selected gauge-row Kronecker selector upgrades the
-- homogeneous zero-norm result to pointwise kernel triviality.  Thus both
-- I+R_A and its rationally weighted conjugate are genuinely injective finite
-- rational endomorphisms, with explicit reopening slack.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateBasisExact as Basis
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanFiniteStrictContractionReopeningExact as Reopen
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as Contraction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundResidualPowerDecayExact as Residual
import DASHI.Physics.YangMills.BalabanSelectedBackgroundRationalWeightedPowerDecayExact as Weighted
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed

GaugeVector : Set
GaugeVector = Contraction.GaugeRow → ℚ

gaugeRowSelector : Basis.FiniteSelector Contraction.GaugeRow
gaugeRowSelector = Rows.selectedGaugeRowFiniteSelector

------------------------------------------------------------------------
-- Finite matrix action respects subtraction exactly.
------------------------------------------------------------------------

applyKernelDifferenceExact :
  ∀ {Index : Set} indices kernel
    (left right : Index → ℚ) row →
  L1.applyKernel indices kernel (Reopen.vectorDifference left right) row
  ≡ L1.applyKernel indices kernel left row
    - L1.applyKernel indices kernel right row
applyKernelDifferenceExact indices kernel left right row =
  let
    leftTerm = λ column → kernel row column * left column
    rightTerm = λ column → kernel row column * right column

    expand :
      L1.applyKernel indices kernel (Reopen.vectorDifference left right) row
      ≡ Sums.sumRational indices
          (λ column → leftTerm column + - rightTerm column)
    expand = Sums.sumRationalCong indices _ _
      (λ column → ℚRing.solve-∀
        (kernel row column) (left column) (right column))

    split :
      Sums.sumRational indices
        (λ column → leftTerm column + - rightTerm column)
      ≡ Sums.sumRational indices leftTerm
        + Sums.sumRational indices (λ column → - rightTerm column)
    split = Mass.sumAddExact indices leftTerm (λ column → - rightTerm column)

    negate :
      Sums.sumRational indices (λ column → - rightTerm column)
      ≡ - Sums.sumRational indices rightTerm
    negate = Sums.sumRationalNegate indices rightTerm
  in
  trans expand
    (trans split
      (trans
        (cong
          (Sums.sumRational indices leftTerm +_)
          negate)
        (ℚRing.solve-∀
          (Sums.sumRational indices leftTerm)
          (Sums.sumRational indices rightTerm))))

------------------------------------------------------------------------
-- Unweighted reopening: 1/10 residual, 10/9 inverse bound.
------------------------------------------------------------------------

unweightedIdentityPlusResidualApply :
  Physical.RationalSU2Background4 → GaugeVector → GaugeVector
unweightedIdentityPlusResidualApply background vector row =
  vector row + Residual.residualApply background vector row

UnweightedReopeningEquation :
  Physical.RationalSU2Background4 → GaugeVector → GaugeVector → Set
UnweightedReopeningEquation background solution source =
  ∀ row → unweightedIdentityPlusResidualApply background solution row
    ≡ source row

unweightedSlack tenNinths : ℚ
unweightedSlack = + 9 / 10
tenNinths = + 10 / 9

unweightedSlackExact :
  Contraction.oneTenth + unweightedSlack ≡ 1ℚ
unweightedSlackExact = ℚRing.solve []

selectedBackgroundResidualReopeningTenNinths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ solution source →
  UnweightedReopeningEquation background solution source →
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ tenNinths * L1.vectorL1 Contraction.gaugeRows source
selectedBackgroundResidualReopeningTenNinths
    background radius solution source equation =
  let
    xNorm = L1.vectorL1 Contraction.gaugeRows solution
    yNorm = L1.vectorL1 Contraction.gaugeRows source
    rNorm = L1.vectorL1 Contraction.gaugeRows
      (Residual.residualApply background solution)

    triangle : xNorm ≤ yNorm + rNorm
    triangle = Reopen.solutionL1ReopeningUpper
      Contraction.gaugeRows
      (Residual.residualApply background)
      solution source equation

    contraction : rNorm ≤ Contraction.oneTenth * xNorm
    contraction = Residual.residualOneStepL1Contraction
      background radius solution

    replaceResidual :
      yNorm + rNorm ≤ yNorm + Contraction.oneTenth * xNorm
    replaceResidual = ℚP.+-monoʳ-≤ yNorm contraction

    beforeGap :
      xNorm ≤ yNorm + Contraction.oneTenth * xNorm
    beforeGap = ℚP.≤-trans triangle replaceResidual

    gapRaw :
      (1ℚ - Contraction.oneTenth) * xNorm ≤ yNorm
    gapRaw = Reopen.reopeningGapBound
      xNorm yNorm Contraction.oneTenth beforeGap

    gap : unweightedSlack * xNorm ≤ yNorm
    gap = subst
      (λ lower → lower ≤ yNorm)
      (cong (_* xNorm)
        (ℚRing.solve [] : 1ℚ - Contraction.oneTenth ≡ unweightedSlack))
      gapRaw

    scaled :
      tenNinths * (unweightedSlack * xNorm)
      ≤ tenNinths * yNorm
    scaled = Norm.scaleNonnegative tenNinths
      (ℚP.nonNegative⁻¹ tenNinths) gap

    leftExact :
      tenNinths * (unweightedSlack * xNorm) ≡ xNorm
    leftExact = ℚRing.solve-∀ xNorm
  in
  subst
    (λ lower → lower ≤ tenNinths * yNorm)
    leftExact scaled

unweightedResidualDifferenceExact :
  ∀ background left right row →
  Residual.residualApply background (Reopen.vectorDifference left right) row
  ≡ Residual.residualApply background left row
    - Residual.residualApply background right row
unweightedResidualDifferenceExact background left right row =
  applyKernelDifferenceExact
    Contraction.gaugeRows
    (Contraction.flatGreenTimesPerturbationKernel background)
    left right row

unweightedDifferenceSolvesHomogeneous :
  ∀ background left right →
  (∀ row →
    unweightedIdentityPlusResidualApply background left row
    ≡ unweightedIdentityPlusResidualApply background right row) →
  UnweightedReopeningEquation background
    (Reopen.vectorDifference left right) Reopen.zeroVector
unweightedDifferenceSolvesHomogeneous background left right equal row =
  let
    residualDifference =
      unweightedResidualDifferenceExact background left right row

    leftValue = unweightedIdentityPlusResidualApply background left row
    rightValue = unweightedIdentityPlusResidualApply background right row

    rearrange :
      (left row - right row)
        + (Residual.residualApply background left row
          - Residual.residualApply background right row)
      ≡ leftValue - rightValue
    rearrange = ℚRing.solve-∀
      (left row) (right row)
      (Residual.residualApply background left row)
      (Residual.residualApply background right row)

    equalZero : leftValue - rightValue ≡ 0ℚ
    equalZero = trans
      (cong (_- rightValue) (equal row))
      (ℚRing.solve-∀ rightValue)
  in
  trans
    (cong
      ((left row - right row) +_)
      residualDifference)
    (trans rearrange equalZero)

oneTenthBelowOneSixth : Contraction.oneTenth ≤ Reopen.oneSixth
oneTenthBelowOneSixth =
  Norm.nonnegativeDifferenceImpliesBelow
    (subst
      (λ value → 0ℚ ≤ value)
      (sym (ℚRing.solve [] :
        Reopen.oneSixth - Contraction.oneTenth ≡ + 1 / 15))
      (ℚP.nonNegative⁻¹ (+ 1 / 15)))

selectedBackgroundResidualIdentityPlusInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ left right →
  (∀ row →
    unweightedIdentityPlusResidualApply background left row
    ≡ unweightedIdentityPlusResidualApply background right row) →
  ∀ row → left row ≡ right row
selectedBackgroundResidualIdentityPlusInjective
    background radius left right equal =
  let
    difference = Reopen.vectorDifference left right
    differenceNorm = L1.vectorL1 Contraction.gaugeRows difference

    equation :
      UnweightedReopeningEquation background difference Reopen.zeroVector
    equation = unweightedDifferenceSolvesHomogeneous
      background left right equal

    residualOneTenth = Residual.residualOneStepL1Contraction
      background radius difference

    scaledCoefficient :
      differenceNorm * Contraction.oneTenth
      ≤ differenceNorm * Reopen.oneSixth
    scaledCoefficient =
      Norm.scaleNonnegative differenceNorm
        (Reopen.vectorL1Nonnegative Contraction.gaugeRows difference)
        oneTenthBelowOneSixth

    scaledCoefficientReordered :
      Contraction.oneTenth * differenceNorm
      ≤ Reopen.oneSixth * differenceNorm
    scaledCoefficientReordered =
      subst
        (λ lower → lower ≤ Reopen.oneSixth * differenceNorm)
        (ℚP.*-comm differenceNorm Contraction.oneTenth)
        (subst
          (λ upper → differenceNorm * Contraction.oneTenth ≤ upper)
          (ℚP.*-comm differenceNorm Reopen.oneSixth)
          scaledCoefficient)

    residualOneSixth :
      L1.vectorL1 Contraction.gaugeRows
        (Residual.residualApply background difference)
      ≤ Reopen.oneSixth * differenceNorm
    residualOneSixth =
      ℚP.≤-trans residualOneTenth scaledCoefficientReordered

    differenceZero : ∀ row → difference row ≡ 0ℚ
    differenceZero =
      Reopen.oneSixthHomogeneousReopeningPointwiseZero
        gaugeRowSelector (Residual.residualApply background)
        difference equation residualOneSixth
  in
  λ row →
    trans
      (sym (ℚRing.solve-∀ (left row) (right row) :
        (left row - right row) + right row ≡ left row))
      (trans
        (cong (_+ right row) (differenceZero row))
        (ℚRing.solve-∀ (right row) : 0ℚ + right row ≡ right row))

------------------------------------------------------------------------
-- Rational Combes--Thomas reopening: 1/6 residual, 6/5 inverse bound.
------------------------------------------------------------------------

weightedIdentityPlusResidualApply :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  GaugeVector → GaugeVector
weightedIdentityPlusResidualApply root background vector row =
  vector row + Weighted.weightedResidualApply root background vector row

WeightedReopeningEquation :
  Contraction.GaugeRow → Physical.RationalSU2Background4 →
  GaugeVector → GaugeVector → Set
WeightedReopeningEquation root background solution source =
  ∀ row → weightedIdentityPlusResidualApply root background solution row
    ≡ source row

weightedSlack : ℚ
weightedSlack = + 5 / 6

weightedSlackExact :
  Reopen.oneSixth + weightedSlack ≡ 1ℚ
weightedSlackExact = ℚRing.solve []

selectedBackgroundWeightedResidualReopeningSixFifths :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root solution source →
  WeightedReopeningEquation root background solution source →
  L1.vectorL1 Contraction.gaugeRows solution
  ≤ Reopen.sixFifths * L1.vectorL1 Contraction.gaugeRows source
selectedBackgroundWeightedResidualReopeningSixFifths
    background radius root solution source equation =
  Reopen.oneSixthReopeningBound
    Contraction.gaugeRows
    (Weighted.weightedResidualApply root background)
    solution source equation
    (Weighted.weightedResidualOneStepL1Contraction
      background radius root solution)

selectedBackgroundWeightedResidualHomogeneousZeroNorm :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root solution →
  WeightedReopeningEquation
    root background solution Reopen.zeroVector →
  L1.vectorL1 Contraction.gaugeRows solution ≡ 0ℚ
selectedBackgroundWeightedResidualHomogeneousZeroNorm
    background radius root solution equation =
  Reopen.oneSixthHomogeneousReopeningZeroNorm
    Contraction.gaugeRows
    (Weighted.weightedResidualApply root background)
    solution equation
    (Weighted.weightedResidualOneStepL1Contraction
      background radius root solution)

weightedResidualDifferenceExact :
  ∀ root background left right row →
  Weighted.weightedResidualApply root background
      (Reopen.vectorDifference left right) row
  ≡ Weighted.weightedResidualApply root background left row
    - Weighted.weightedResidualApply root background right row
weightedResidualDifferenceExact root background left right row =
  applyKernelDifferenceExact
    Contraction.gaugeRows
    (Weighted.Weight.weightedSelectedBackgroundResidual root background)
    left right row

weightedDifferenceSolvesHomogeneous :
  ∀ root background left right →
  (∀ row →
    weightedIdentityPlusResidualApply root background left row
    ≡ weightedIdentityPlusResidualApply root background right row) →
  WeightedReopeningEquation root background
    (Reopen.vectorDifference left right) Reopen.zeroVector
weightedDifferenceSolvesHomogeneous root background left right equal row =
  let
    residualDifference =
      weightedResidualDifferenceExact root background left right row

    leftValue = weightedIdentityPlusResidualApply root background left row
    rightValue = weightedIdentityPlusResidualApply root background right row

    rearrange :
      (left row - right row)
        + (Weighted.weightedResidualApply root background left row
          - Weighted.weightedResidualApply root background right row)
      ≡ leftValue - rightValue
    rearrange = ℚRing.solve-∀
      (left row) (right row)
      (Weighted.weightedResidualApply root background left row)
      (Weighted.weightedResidualApply root background right row)

    equalZero : leftValue - rightValue ≡ 0ℚ
    equalZero = trans
      (cong (_- rightValue) (equal row))
      (ℚRing.solve-∀ rightValue)
  in
  trans
    (cong
      ((left row - right row) +_)
      residualDifference)
    (trans rearrange equalZero)

selectedBackgroundWeightedResidualIdentityPlusInjective :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ root left right →
  (∀ row →
    weightedIdentityPlusResidualApply root background left row
    ≡ weightedIdentityPlusResidualApply root background right row) →
  ∀ row → left row ≡ right row
selectedBackgroundWeightedResidualIdentityPlusInjective
    background radius root left right equal =
  let
    difference = Reopen.vectorDifference left right

    equation :
      WeightedReopeningEquation root background difference Reopen.zeroVector
    equation = weightedDifferenceSolvesHomogeneous
      root background left right equal

    differenceZero : ∀ row → difference row ≡ 0ℚ
    differenceZero =
      Reopen.oneSixthHomogeneousReopeningPointwiseZero
        gaugeRowSelector
        (Weighted.weightedResidualApply root background)
        difference equation
        (Weighted.weightedResidualOneStepL1Contraction
          background radius root difference)
  in
  λ row →
    trans
      (sym (ℚRing.solve-∀ (left row) (right row) :
        (left row - right row) + right row ≡ left row))
      (trans
        (cong (_+ right row) (differenceZero row))
        (ℚRing.solve-∀ (right row) : 0ℚ + right row ≡ right row))

selectedBackgroundGreenUnweightedSlackLevel : ProofLevel
selectedBackgroundGreenUnweightedSlackLevel = machineChecked

selectedBackgroundGreenWeightedSlackLevel : ProofLevel
selectedBackgroundGreenWeightedSlackLevel = machineChecked

selectedBackgroundResidualIdentityPlusInjectiveLevel : ProofLevel
selectedBackgroundResidualIdentityPlusInjectiveLevel = machineChecked

selectedBackgroundWeightedResidualIdentityPlusInjectiveLevel : ProofLevel
selectedBackgroundWeightedResidualIdentityPlusInjectiveLevel = machineChecked

selectedBackgroundWeightedReopeningSixFifthsLevel : ProofLevel
selectedBackgroundWeightedReopeningSixFifthsLevel = machineChecked
