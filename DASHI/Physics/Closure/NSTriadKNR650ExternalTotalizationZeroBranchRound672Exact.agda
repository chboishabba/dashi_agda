{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650ExternalTotalizationZeroBranchRound672Exact where

------------------------------------------------------------------------
-- ROUND672 / R606 EXTERNAL FOLD = R630 TOTAL COMMUTATOR + EXPLICIT p=0 DEFECT
--
-- R606's external-network contribution is built from the literal R230 external
-- product-rule forcing on the complete fixed-output fibre.  For a fixed
-- spectator beta, R541 supplies the swap-invariant R294 resolvent weight.
--
-- R670 closes the weighted external product-rule -> commutator reindexing.
-- R671 then identifies the raw weighted external commutator with R630 on the
-- p != 0 branch, but correctly refuses to erase R630's explicit p = 0 branch.
--
-- This owner closes the strongest unconditional vector-level splice:
--
--   fold [ W * R606.externalDoubleForcing ]
--     =
--   fold [ R630.totalExternalNestedCommutator ]
--     + fold [ explicitPZeroDefect ].
--
-- The defect is exactly the raw weighted nested external commutator on p = 0
-- incidences and zero elsewhere.  No claim that this defect vanishes is made.
--
-- Consequently the mature R631/R636/R637 totalized external-helicity route is
-- now the canonical nonzero contribution, while the only representation debt
-- left at this layer is an explicit zero-branch fold.  No estimate, norm,
-- absolute value, or new Clay-facing analytic leaf is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNLerayComplexScalarLinearityRound73Exact as R73
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNDoubleMixedAsSwapPairedPlusMinusRound387Exact as R387
import DASHI.Physics.Closure.NSTriadKNR567ForcingFullSelfExternalSplitRound606Exact as R606
import DASHI.Physics.Closure.NSTriadKNExternalWeightedSlotCommutatorTotalRound630Exact as R630
import DASHI.Physics.Closure.NSTriadKNR650WeightedExternalProductRuleCommutatorRound670Exact as R670
import DASHI.Physics.Closure.NSTriadKNR650ExternalTotalizationNonzeroWeldRound671Exact as R671

module ExternalTotalization672
    {r} {F : C3.RealField r}
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode))
    (W : R294.SwapInvariantCellWeight F) where

  system = Field30.finiteSystem physicalSystem
  cutoff = Audit.cutoff system

  module Weighted = R670.WeightedExternal physicalSystem S W

  module Weld =
    R671.NonzeroWeld
      W S L H system velocityTransverse

  module Total =
    R630.TotalExternalCommutator630
      W S L H system velocityTransverse

  weightedProductRule :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedProductRule = Weighted.weightedProductRule

  weightedCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 F
  weightedCommutator = Weighted.weightedCommutator

  module AtOutput (output : Z3.FourierMode) where

    module Split = R606.FixedOutput physicalSystem S output

    fibre : List Physical.PhysicalTriadIncidence
    fibre = Output.physicalOutputFiber cutoff output

    weightedExternalDoubleForcing :
      Physical.PhysicalTriadIncidence → C3.Complex3 F
    weightedExternalDoubleForcing tau =
      C3.complex3Scale
        (R294.weight W tau)
        (Split.externalDoubleForcing tau)

    weightedSwapProductRule :
      Physical.PhysicalTriadIncidence → C3.Complex3 F
    weightedSwapProductRule tau =
      C3.complex3Scale
        (R294.weight W tau)
        (Split.Net.externalProductRuleCell (Symmetry.swapTriad tau))

    weightedSwapProductRuleIsProductAfterSwap :
      (tau : Physical.PhysicalTriadIncidence) →
      weightedSwapProductRule tau
      ≡ weightedProductRule (Symmetry.swapTriad tau)
    weightedSwapProductRuleIsProductAfterSwap tau =
      cong
        (λ selectedWeight →
          C3.complex3Scale selectedWeight
            (Split.Net.externalProductRuleCell (Symmetry.swapTriad tau)))
        (sym (R294.swapInvariant W tau))

    weightedExternalDoublePointwise :
      (tau : Physical.PhysicalTriadIncidence) →
      weightedExternalDoubleForcing tau
      ≡
      C3.complex3Add
        (C3.complex3Add
          (weightedProductRule tau)
          (weightedProductRule tau))
        (C3.complex3Add
          (weightedSwapProductRule tau)
          (weightedSwapProductRule tau))
    weightedExternalDoublePointwise tau =
      let
        w = R294.weight W tau
        f = Split.Net.externalProductRuleCell tau
        fs = Split.Net.externalProductRuleCell (Symmetry.swapTriad tau)
      in
      trans
        (R73.complex3ScaleAdd
          w (R387.doublePlus f) (R387.doublePlus fs))
        (cong₂ C3.complex3Add
          (R73.complex3ScaleAdd w f f)
          (R73.complex3ScaleAdd w fs fs))

    foldCongruent :
      (left right :
        Physical.PhysicalTriadIncidence → C3.Complex3 F) →
      ((tau : Physical.PhysicalTriadIncidence) → left tau ≡ right tau) →
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector left items ≡ R224.foldVector right items
    foldCongruent left right pointwise [] = refl
    foldCongruent left right pointwise (tau ∷ rest) =
      cong₂ C3.complex3Add
        (pointwise tau)
        (foldCongruent left right pointwise rest)

    foldSwapProductRuleIsFoldProductRule :
      R224.foldVector weightedSwapProductRule fibre
      ≡ R224.foldVector weightedProductRule fibre
    foldSwapProductRuleIsFoldProductRule =
      trans
        (foldSwapPointwise fibre)
        (trans
          (sym
            (R224.foldMap weightedProductRule Symmetry.swapTriad fibre))
          (R224.foldPermutationInvariant weightedProductRule
            (R224.swapOutputFibrePermutation cutoff output)))
      where
      foldSwapPointwise :
        (items : List Physical.PhysicalTriadIncidence) →
        R224.foldVector weightedSwapProductRule items
        ≡
        R224.foldVector
          (λ tau → weightedProductRule (Symmetry.swapTriad tau))
          items
      foldSwapPointwise [] = refl
      foldSwapPointwise (tau ∷ rest) =
        cong₂ C3.complex3Add
          (weightedSwapProductRuleIsProductAfterSwap tau)
          (foldSwapPointwise rest)

    foldFourProductComponents :
      R224.foldVector
        (λ tau →
          C3.complex3Add
            (C3.complex3Add
              (weightedProductRule tau)
              (weightedProductRule tau))
            (C3.complex3Add
              (weightedSwapProductRule tau)
              (weightedSwapProductRule tau)))
        fibre
      ≡
      C3.complex3Add
        (C3.complex3Add
          (R224.foldVector weightedProductRule fibre)
          (R224.foldVector weightedProductRule fibre))
        (C3.complex3Add
          (R224.foldVector weightedSwapProductRule fibre)
          (R224.foldVector weightedSwapProductRule fibre))
    foldFourProductComponents =
      trans
        (R230.foldAdd
          (λ tau →
            C3.complex3Add
              (weightedProductRule tau)
              (weightedProductRule tau))
          (λ tau →
            C3.complex3Add
              (weightedSwapProductRule tau)
              (weightedSwapProductRule tau))
          fibre)
        (cong₂ C3.complex3Add
          (R230.foldAdd weightedProductRule weightedProductRule fibre)
          (R230.foldAdd
            weightedSwapProductRule weightedSwapProductRule fibre))

    weightedExternalDoubleFoldIsFourProductFolds :
      let
        P = R224.foldVector weightedProductRule fibre
      in
      R224.foldVector weightedExternalDoubleForcing fibre
      ≡ C3.complex3Add
          (C3.complex3Add P P)
          (C3.complex3Add P P)
    weightedExternalDoubleFoldIsFourProductFolds =
      let
        P = R224.foldVector weightedProductRule fibre
      in
      trans
        (foldCongruent
          weightedExternalDoubleForcing
          (λ tau →
            C3.complex3Add
              (C3.complex3Add
                (weightedProductRule tau)
                (weightedProductRule tau))
              (C3.complex3Add
                (weightedSwapProductRule tau)
                (weightedSwapProductRule tau)))
          weightedExternalDoublePointwise
          fibre)
        (trans
          foldFourProductComponents
          (cong
            (λ Sfold →
              C3.complex3Add
                (C3.complex3Add P P)
                (C3.complex3Add Sfold Sfold))
            foldSwapProductRuleIsFoldProductRule))

    weightedExternalDoubleFoldIsFourCommutatorFolds :
      let
        C = R224.foldVector weightedCommutator fibre
      in
      R224.foldVector weightedExternalDoubleForcing fibre
      ≡ C3.complex3Add
          (C3.complex3Add C C)
          (C3.complex3Add C C)
    weightedExternalDoubleFoldIsFourCommutatorFolds =
      let
        productToCommutator =
          Weighted.fixedOutputWeightedExternalProductRuleIsCommutator
            cutoff output
      in
      trans
        weightedExternalDoubleFoldIsFourProductFolds
        (cong
          (λ P →
            C3.complex3Add
              (C3.complex3Add P P)
              (C3.complex3Add P P))
          productToCommutator)

    rawWeightedDoubleIsTwoCommutators :
      (tau : Physical.PhysicalTriadIncidence) →
      Weld.rawWeightedDoubleExternalCommutator tau
      ≡
      C3.complex3Add
        (weightedCommutator tau)
        (weightedCommutator tau)
    rawWeightedDoubleIsTwoCommutators tau =
      R73.complex3ScaleAdd
        (R294.weight W tau)
        (Weighted.Ext.externalCommutatorCell tau)
        (Weighted.Ext.externalCommutatorCell tau)

    rawWeightedNestedIsFourCommutators :
      (tau : Physical.PhysicalTriadIncidence) →
      Weld.rawWeightedNestedExternalCommutator tau
      ≡
      C3.complex3Add
        (C3.complex3Add
          (weightedCommutator tau)
          (weightedCommutator tau))
        (C3.complex3Add
          (weightedCommutator tau)
          (weightedCommutator tau))
    rawWeightedNestedIsFourCommutators tau =
      cong₂ C3.complex3Add
        (rawWeightedDoubleIsTwoCommutators tau)
        (rawWeightedDoubleIsTwoCommutators tau)

    rawNestedFoldIsFourCommutatorFolds :
      let
        C = R224.foldVector weightedCommutator fibre
      in
      R224.foldVector Weld.rawWeightedNestedExternalCommutator fibre
      ≡ C3.complex3Add
          (C3.complex3Add C C)
          (C3.complex3Add C C)
    rawNestedFoldIsFourCommutatorFolds =
      trans
        (foldCongruent
          Weld.rawWeightedNestedExternalCommutator
          (λ tau →
            C3.complex3Add
              (C3.complex3Add
                (weightedCommutator tau)
                (weightedCommutator tau))
              (C3.complex3Add
                (weightedCommutator tau)
                (weightedCommutator tau)))
          rawWeightedNestedIsFourCommutators
          fibre)
        (trans
          (R230.foldAdd
            (λ tau →
              C3.complex3Add
                (weightedCommutator tau)
                (weightedCommutator tau))
            (λ tau →
              C3.complex3Add
                (weightedCommutator tau)
                (weightedCommutator tau))
            fibre)
          (cong₂ C3.complex3Add
            (R230.foldAdd
              weightedCommutator weightedCommutator fibre)
            (R230.foldAdd
              weightedCommutator weightedCommutator fibre)))

    weightedExternalDoubleFoldIsRawNestedFold :
      R224.foldVector weightedExternalDoubleForcing fibre
      ≡ R224.foldVector Weld.rawWeightedNestedExternalCommutator fibre
    weightedExternalDoubleFoldIsRawNestedFold =
      trans
        weightedExternalDoubleFoldIsFourCommutatorFolds
        (sym rawNestedFoldIsFourCommutatorFolds)

    pZeroNestedDefect :
      Physical.PhysicalTriadIncidence → C3.Complex3 F
    pZeroNestedDefect tau
      with Output.modeEqual (Physical.p tau) Z3.zeroMode
    ... | true = Weld.rawWeightedNestedExternalCommutator tau
    ... | false = C3.complex3Zero F

    rawNestedIsTotalPlusPZeroDefect :
      (tau : Physical.PhysicalTriadIncidence) →
      Weld.rawWeightedNestedExternalCommutator tau
      ≡
      C3.complex3Add
        (Total.totalExternalNestedCommutator tau)
        (pZeroNestedDefect tau)
    rawNestedIsTotalPlusPZeroDefect tau
        with Output.modeEqual (Physical.p tau) Z3.zeroMode in decision
    ... | true =
      sym
        (R230.complex3AddZeroLeft
          (Weld.rawWeightedNestedExternalCommutator tau))
    ... | false =
      trans
        (Weld.rawNestedEqualsTotalOnPNonzero
          tau (Total.pNonzeroFromFalse tau decision))
        (sym
          (Algebra.complex3AddZeroRight
            (Total.totalExternalNestedCommutator tau)))

    rawNestedFoldIsTotalPlusPZeroDefect :
      R224.foldVector Weld.rawWeightedNestedExternalCommutator fibre
      ≡
      C3.complex3Add
        (R224.foldVector Total.totalExternalNestedCommutator fibre)
        (R224.foldVector pZeroNestedDefect fibre)
    rawNestedFoldIsTotalPlusPZeroDefect =
      trans
        (foldCongruent
          Weld.rawWeightedNestedExternalCommutator
          (λ tau →
            C3.complex3Add
              (Total.totalExternalNestedCommutator tau)
              (pZeroNestedDefect tau))
          rawNestedIsTotalPlusPZeroDefect
          fibre)
        (R230.foldAdd
          Total.totalExternalNestedCommutator
          pZeroNestedDefect
          fibre)

    fixedOutputR606ExternalFoldIsTotalPlusPZeroDefect :
      R224.foldVector weightedExternalDoubleForcing fibre
      ≡
      C3.complex3Add
        (R224.foldVector Total.totalExternalNestedCommutator fibre)
        (R224.foldVector pZeroNestedDefect fibre)
    fixedOutputR606ExternalFoldIsTotalPlusPZeroDefect =
      trans
        weightedExternalDoubleFoldIsRawNestedFold
        rawNestedFoldIsTotalPlusPZeroDefect

------------------------------------------------------------------------
-- Status / zero-branch firewall.
------------------------------------------------------------------------

round672R606WeightedExternalFoldTotalizesThroughR630 : Bool
round672R606WeightedExternalFoldTotalizesThroughR630 = true

round672PZeroBranchRetainedExplicitly : Bool
round672PZeroBranchRetainedExplicitly = true

round672PZeroDefectProvedZero : Bool
round672PZeroDefectProvedZero = false

round672R606ExternalFoldEqualsR630WithoutDefect : Bool
round672R606ExternalFoldEqualsR630WithoutDefect = false

round672IntroducesEstimate : Bool
round672IntroducesEstimate = false

round672IntroducesNewClayLeaf : Bool
round672IntroducesNewClayLeaf = false

round672ClayPromotion : Bool
round672ClayPromotion = false

round672R606WeightedExternalFoldTotalizesThroughR630IsTrue :
  round672R606WeightedExternalFoldTotalizesThroughR630 ≡ true
round672R606WeightedExternalFoldTotalizesThroughR630IsTrue = refl

round672PZeroBranchRetainedExplicitlyIsTrue :
  round672PZeroBranchRetainedExplicitly ≡ true
round672PZeroBranchRetainedExplicitlyIsTrue = refl

round672PZeroDefectProvedZeroIsFalse :
  round672PZeroDefectProvedZero ≡ false
round672PZeroDefectProvedZeroIsFalse = refl

round672R606ExternalFoldEqualsR630WithoutDefectIsFalse :
  round672R606ExternalFoldEqualsR630WithoutDefect ≡ false
round672R606ExternalFoldEqualsR630WithoutDefectIsFalse = refl

round672IntroducesEstimateIsFalse :
  round672IntroducesEstimate ≡ false
round672IntroducesEstimateIsFalse = refl

round672IntroducesNewClayLeafIsFalse :
  round672IntroducesNewClayLeaf ≡ false
round672IntroducesNewClayLeafIsFalse = refl

round672ClayPromotionIsFalse :
  round672ClayPromotion ≡ false
round672ClayPromotionIsFalse = refl
