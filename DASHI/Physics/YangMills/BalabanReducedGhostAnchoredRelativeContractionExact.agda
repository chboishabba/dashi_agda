module DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- DASHI CONTRIBUTION
--
-- The selected Green lane already proves row/column contraction for G0 E_A,
-- but the literal reduced ghost operator uses the ANCHORED inverse
--
--   H_x0 s = G0 s - (G0 s)(x0).
--
-- We do not assume E_A annihilates constant gauge parameters at a non-flat
-- background.  Instead we bound the actual anchored Green directly:
--
--   rowMass(H_x0) <= 2 (17/16) = 17/8.
--
-- The physical FP=Gram theorem identifies M_A-M_0 with the same selected Gram
-- perturbation E_A.  Hence on colourwise mean-zero sources
--
--   R_A = (M_A-M_0) H_x0 = E_A H_x0,
--
-- and the exact selected perturbation mass 6153/65536 gives
--
--   rowMass(E_A H_x0)
--     <= (6153/65536)(17/8)
--      = 104601/524288 < 1/5 < 1.
--
-- This is a strict contraction for the ACTUAL anchored reduced relative FP
-- operator, without silently replacing the anchored section by the
-- translation-invariant Green representative.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; _≤_; _<_; _/_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact as Fubini
import DASHI.Physics.YangMills.BalabanFiniteRectangularRationalExact as Rect
import DASHI.Physics.YangMills.BalabanFiniteRectangularAbsoluteMassExact as Mass
import DASHI.Physics.YangMills.BalabanP33FiniteWeightedSchurSquaredExact as Schur
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as KKT
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Coordinates
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as FlatGauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanP33PhysicalFaddeevPopovOperatorExact as FP
import DASHI.Physics.YangMills.BalabanReducedFlatFaddeevPopovGreenInverseExact as ReducedInverse
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovRelativePerturbationExact as Relative
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeFaddeevPopovGramExact as FPGram
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeConstraintMatrixExact as GaugeMatrix
import DASHI.Physics.YangMills.BalabanSelectedCombinedConstraintRowCarrierExact as Rows
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationFiniteRangeExact as Perturbation
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugePerturbationActionExact as PerturbationAction
import DASHI.Physics.YangMills.BalabanSelectedBackgroundGaugeGramPerturbationAbsoluteMassExact as PerturbationMass
import DASHI.Physics.YangMills.BalabanSelectedBackgroundFlatGreenPerturbationContractionExact as GreenContraction
import DASHI.Physics.YangMills.BalabanSelectedFlatGaugeGreenAbsoluteMassExact as GreenMass
import DASHI.Physics.YangMills.BalabanSZZStrongCouplingDecisionExact as Order

GaugeRow : Set
GaugeRow = FlatGauge.GaugeCoordinate4

gaugeRows = GreenContraction.gaugeRows

------------------------------------------------------------------------
-- Literal anchored Green kernel H_x0.
------------------------------------------------------------------------

anchoredGreenKernel : Periodic.Site4 → GaugeRow → GaugeRow → ℚ
anchoredGreenKernel anchor
    (pair outputCoordinate outputSite) input =
  GreenContraction.flatGreenKernelMatrix
      (pair outputCoordinate outputSite) input
  - GreenContraction.flatGreenKernelMatrix
      (pair outputCoordinate anchor) input

anchoredGreenApply :
  Periodic.Site4 → FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
anchoredGreenApply anchor source =
  Rect.applyRectangular Rows.selectedGaugeRowCarrier
    (anchoredGreenKernel anchor) source

anchoredGreenApplyIsReducedInverse :
  ∀ anchor source coordinate site →
  anchoredGreenApply anchor source (pair coordinate site)
  ≡ ReducedInverse.reducedFlatGreenInverse source anchor
      (pair coordinate site)
anchoredGreenApplyIsReducedInverse anchor source coordinate site =
  let
    output = pair coordinate site
    anchorOutput = pair coordinate anchor

    split = Fubini.sumRationalSubtract gaugeRows
      (λ input →
        GreenContraction.flatGreenKernelMatrix output input * source input)
      (λ input →
        GreenContraction.flatGreenKernelMatrix anchorOutput input * source input)

    currentExact = GreenContraction.flatGreenKernelActsExactly
      source coordinate site
    anchorExact = GreenContraction.flatGreenKernelActsExactly
      source coordinate anchor
  in
  trans split
    (trans (cong₂ _-_ currentExact anchorExact) refl)

------------------------------------------------------------------------
-- Absolute row mass of H_x0.
------------------------------------------------------------------------

absoluteDifferenceTriangle : ∀ left right →
  ∣ left - right ∣ ≤ ∣ left ∣ + ∣ right ∣
absoluteDifferenceTriangle left right =
  let
    subtractAsAdd : left - right ≡ left + (- right)
    subtractAsAdd = ℚRing.solve-∀ left right
    raw = ℚP.∣p+q∣≤∣p∣+∣q∣ left (- right)
    negAbs = ℚP.∣-p∣≡∣p∣ right
  in
  subst
    (λ lower → lower ≤ ∣ left ∣ + ∣ right ∣)
    (cong ∣_∣ subtractAsAdd)
    (subst
      (λ upper → ∣ left + (- right) ∣ ≤ ∣ left ∣ + upper)
      negAbs raw)

anchoredGreenRowMassBound : ℚ
anchoredGreenRowMassBound = + 17 / 8

anchoredGreenAbsoluteRowMass : Periodic.Site4 → GaugeRow → ℚ
anchoredGreenAbsoluteRowMass anchor row =
  Mass.squareRowMass gaugeRows (anchoredGreenKernel anchor) row

anchoredGreenRowMassBelowSeventeenEighths :
  ∀ anchor row →
  anchoredGreenAbsoluteRowMass anchor row ≤ anchoredGreenRowMassBound
anchoredGreenRowMassBelowSeventeenEighths
    anchor (pair outputCoordinate outputSite) =
  let
    output = pair outputCoordinate outputSite
    anchorOutput = pair outputCoordinate anchor

    triangle = Schur.sumPointwiseBelow gaugeRows
      (λ input → ∣ anchoredGreenKernel anchor output input ∣)
      (λ input →
        ∣ GreenContraction.flatGreenKernelMatrix output input ∣
        + ∣ GreenContraction.flatGreenKernelMatrix anchorOutput input ∣)
      (λ input → absoluteDifferenceTriangle
        (GreenContraction.flatGreenKernelMatrix output input)
        (GreenContraction.flatGreenKernelMatrix anchorOutput input))

    split = Mass.sumAddExact gaugeRows
      (λ input → ∣ GreenContraction.flatGreenKernelMatrix output input ∣)
      (λ input → ∣ GreenContraction.flatGreenKernelMatrix anchorOutput input ∣)

    both = ℚP.+-mono-≤
      (GreenContraction.selectedFlatGaugeGreenAbsoluteRowMassBound output)
      (GreenContraction.selectedFlatGaugeGreenAbsoluteRowMassBound anchorOutput)

    coefficientExact :
      GreenMass.seventeenSixteenths + GreenMass.seventeenSixteenths
      ≡ anchoredGreenRowMassBound
    coefficientExact = ℚRing.solve []
  in
  ℚP.≤-trans triangle
    (subst
      (λ upper →
        Sums.sumRational gaugeRows
          (λ input →
            ∣ GreenContraction.flatGreenKernelMatrix output input ∣
            + ∣ GreenContraction.flatGreenKernelMatrix anchorOutput input ∣)
        ≤ upper)
      coefficientExact
      (subst
        (λ lower → lower ≤
          GreenMass.seventeenSixteenths + GreenMass.seventeenSixteenths)
        (sym split) both))

------------------------------------------------------------------------
-- Relative kernel E_A H_x0 and same-object identification.
------------------------------------------------------------------------

anchoredRelativeKernel :
  Physical.RationalSU2Background4 → Periodic.Site4 →
  GaugeRow → GaugeRow → ℚ
anchoredRelativeKernel background anchor =
  Rect.composeRectangular Rows.selectedGaugeRowCarrier
    (Perturbation.gaugeGramPerturbationMatrix background)
    (anchoredGreenKernel anchor)

anchoredRelativeApply :
  Physical.RationalSU2Background4 → Periodic.Site4 →
  FP.SiteGaugeParameter4 → FP.SiteGaugeParameter4
anchoredRelativeApply background anchor =
  Rect.applyRectangular Rows.selectedGaugeRowCarrier
    (anchoredRelativeKernel background anchor)

anchoredRelativeApplyExact :
  ∀ background anchor source row →
  anchoredRelativeApply background anchor source row
  ≡ PerturbationAction.selectedGaugeGramPerturbationApply background
      (anchoredGreenApply anchor source) row
anchoredRelativeApplyExact background anchor source row =
  Rect.applyComposeRectangularExact
    Rows.selectedGaugeRowCarrier Rows.selectedGaugeRowCarrier
    (Perturbation.gaugeGramPerturbationMatrix background)
    (anchoredGreenKernel anchor) source row

selectedGaugeGramApplyIsFaddeevPopov :
  ∀ background multiplier row →
  PerturbationAction.selectedGaugeGramMatrixApply background multiplier row
  ≡ FP.faddeevPopovApply background multiplier row
selectedGaugeGramApplyIsFaddeevPopov background multiplier row =
  trans
    (Rect.applyComposeRectangularExact
      KKT.physicalStateCarrier Rows.selectedGaugeRowCarrier
      (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background)
      (Rect.transposeRectangular
        (GaugeMatrix.selectedBackgroundGaugeConstraintMatrix background))
      multiplier row)
    (sym (FPGram.faddeevPopovIsGaugeGram background multiplier row))

anchoredRelativeIsPhysicalReducedFP :
  ∀ background anchor source →
  ReducedInverse.ColourwiseMeanZero source →
  ∀ row →
  anchoredRelativeApply background anchor source row
  ≡ Relative.relativeFaddeevPopovPerturbation
      background anchor source row
anchoredRelativeIsPhysicalReducedFP
    background anchor source meanZero (pair coordinate site) =
  let
    reduced = ReducedInverse.reducedFlatGreenInverse source anchor

    kernelToReduced : ∀ row →
      anchoredGreenApply anchor source row ≡ reduced row
    kernelToReduced (pair colour currentSite) =
      anchoredGreenApplyIsReducedInverse
        anchor source colour currentSite

    perturbationAction =
      anchoredRelativeApplyExact background anchor source (pair coordinate site)

    perturbationDifference =
      PerturbationAction.selectedGaugeGramPerturbationDifferenceExact
        background (anchoredGreenApply anchor source) (pair coordinate site)

    backgroundFP = selectedGaugeGramApplyIsFaddeevPopov
      background (anchoredGreenApply anchor source) (pair coordinate site)

    identityFP = selectedGaugeGramApplyIsFaddeevPopov
      Physical.identityBackground (anchoredGreenApply anchor source)
      (pair coordinate site)

    backgroundReduced = cong
      (λ parameter →
        FP.faddeevPopovApply background parameter (pair coordinate site))
      (kernelToReduced (pair coordinate site))

    identityReduced = cong
      (λ parameter →
        FP.faddeevPopovApply Physical.identityBackground parameter
          (pair coordinate site))
      (kernelToReduced (pair coordinate site))

    flatIsFlat = FP.identityFaddeevPopovIsFlat reduced coordinate site
    rightInverse = ReducedInverse.reducedFlatGreenRightInverse
      source anchor meanZero coordinate site
  in
  trans perturbationAction
    (trans perturbationDifference
      (trans
        (cong₂ _-_ backgroundFP identityFP)
        (trans
          (cong₂ _-_ backgroundReduced identityReduced)
          (trans
            (cong
              (FP.faddeevPopovApply background reduced (pair coordinate site) -_)
              flatIsFlat)
            (trans
              (cong
                (FP.faddeevPopovApply background reduced (pair coordinate site) -_)
                rightInverse)
              refl)))))

------------------------------------------------------------------------
-- Strict absolute-row contraction.
------------------------------------------------------------------------

transposeAnchoredGreen : Periodic.Site4 → GaugeRow → GaugeRow → ℚ
transposeAnchoredGreen anchor output middle =
  anchoredGreenKernel anchor middle output

anchoredRelativeAsTransposeProduct :
  ∀ background anchor row output →
  anchoredRelativeKernel background anchor row output
  ≡ Mass.transposeProduct gaugeRows
      (Perturbation.gaugeGramPerturbationMatrix background)
      (transposeAnchoredGreen anchor) row output
anchoredRelativeAsTransposeProduct background anchor row output = refl

transposeAnchoredGreenColumnMass : ∀ anchor column →
  Mass.absoluteRectColumnMass gaugeRows
    (transposeAnchoredGreen anchor) column
  ≡ anchoredGreenAbsoluteRowMass anchor column
transposeAnchoredGreenColumnMass anchor column = refl

anchoredRelativeContractionBound : ℚ
anchoredRelativeContractionBound = + 104601 / 524288

anchoredRelativeContractionExactProduct :
  PerturbationMass.perturbationRowMassBound * anchoredGreenRowMassBound
  ≡ anchoredRelativeContractionBound
anchoredRelativeContractionExactProduct = ℚRing.solve []

anchoredRelativeAbsoluteRowMassBound :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ anchor row →
  Mass.squareRowMass gaugeRows
    (anchoredRelativeKernel background anchor) row
  ≤ anchoredRelativeContractionBound
anchoredRelativeAbsoluteRowMassBound background radius anchor row =
  let
    raw = Mass.transposeProductRowMassBound
      gaugeRows gaugeRows
      (Perturbation.gaugeGramPerturbationMatrix background)
      (transposeAnchoredGreen anchor)
      anchoredGreenRowMassBound row
      (ℚP.nonNegative⁻¹ anchoredGreenRowMassBound)
      (λ column →
        subst
          (λ lower → lower ≤ anchoredGreenRowMassBound)
          (sym (transposeAnchoredGreenColumnMass anchor column))
          (anchoredGreenRowMassBelowSeventeenEighths anchor column))

    scaled = PerturbationMass.rightScaleMonotone
      anchoredGreenRowMassBound
      (Mass.squareRowMass gaugeRows
        (Perturbation.gaugeGramPerturbationMatrix background) row)
      PerturbationMass.perturbationRowMassBound
      (ℚP.nonNegative⁻¹ anchoredGreenRowMassBound)
      (PerturbationMass.selectedGaugeGramPerturbationAbsoluteRowMassBound
        background radius row)

    productBound = ℚP.≤-trans raw
      (subst
        (λ upper →
          Mass.squareRowMass gaugeRows
            (Perturbation.gaugeGramPerturbationMatrix background) row
            * anchoredGreenRowMassBound
          ≤ upper)
        anchoredRelativeContractionExactProduct scaled)

    kernelExact = Sums.sumRationalCong gaugeRows _ _
      (λ output → cong ∣_∣
        (anchoredRelativeAsTransposeProduct background anchor row output))
  in
  subst
    (λ lower → lower ≤ anchoredRelativeContractionBound)
    (sym kernelExact) productBound

oneFifth : ℚ
oneFifth = + 1 / 5

anchoredRelativeContractionBelowOneFifth :
  anchoredRelativeContractionBound < oneFifth
anchoredRelativeContractionBelowOneFifth =
  let
    slack : ℚ
    slack = + 1283 / 2621440
    slackExact : oneFifth - anchoredRelativeContractionBound ≡ slack
    slackExact = ℚRing.solve []
    positiveSlack : 0ℚ < oneFifth - anchoredRelativeContractionBound
    positiveSlack = subst
      (λ value → 0ℚ < value)
      (sym slackExact)
      (ℚP.positive⁻¹ slack)
  in
  Order.positiveDifferenceImpliesLess
    oneFifth anchoredRelativeContractionBound positiveSlack

oneFifthBelowOne : oneFifth < 1ℚ
oneFifthBelowOne =
  let
    slack : ℚ
    slack = + 4 / 5
    slackExact : 1ℚ - oneFifth ≡ slack
    slackExact = ℚRing.solve []
    positiveSlack : 0ℚ < 1ℚ - oneFifth
    positiveSlack = subst
      (λ value → 0ℚ < value)
      (sym slackExact)
      (ℚP.positive⁻¹ slack)
  in
  Order.positiveDifferenceImpliesLess 1ℚ oneFifth positiveSlack

anchoredRelativeContractionStrictlyBelowOne :
  anchoredRelativeContractionBound < 1ℚ
anchoredRelativeContractionStrictlyBelowOne =
  ℚP.<-trans anchoredRelativeContractionBelowOneFifth oneFifthBelowOne

reducedGhostAnchoredGreenIdentificationLevel : ProofLevel
reducedGhostAnchoredGreenIdentificationLevel = machineChecked
reducedGhostAnchoredRelativeSameObjectLevel : ProofLevel
reducedGhostAnchoredRelativeSameObjectLevel = machineChecked
reducedGhostAnchoredRelativeContractionLevel : ProofLevel
reducedGhostAnchoredRelativeContractionLevel = machineChecked
