{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact where

------------------------------------------------------------------------
-- ROUND406 / LITERAL SELECTED CMP116 TERMWISE LOCALIZATION
--
-- R404 and R405 already pay the two finite positive summation compilers:
--
--   differentiated terms
--     -> common-Y absolute contribution
--     -> selected connecting-shell boundary bound.
--
-- The remaining P0 leaf is not another summation theorem.  It is the
-- source/application replay which supplies, on the SAME selected carrier:
--
--   * the selected T5/RG density;
--   * the actual observable-indexed J_L/J_R insertions;
--   * the CMP116 decoupling-boundary assignment;
--   * the literal CMP99/CMP109 factorwise ordinary/marked estimates inside
--     each differentiated CMP116 generalized-walk/local-activity term.
--
-- Round72 already proves that those factorwise estimates telescope into a
-- whole differentiated-product majorant.  Therefore this owner must not take
-- `|term| <= termMajorant` as an opaque physical field.  It derives that
-- inequality mechanically and leaves only the literal source factor bounds as
-- the P0a/P0b replay obligation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _-ℝ_ ; absℝ ; _≤ℝ_ )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP116AbsoluteWalkResummationRound404Exact as R404
import DASHI.Physics.YangMills.BalabanCMP116NestedSourceSummationRound405Exact as R405
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact as FactorProduct

------------------------------------------------------------------------
-- The source/application coordinates are carried by the existing selected
-- R318 carrier.  No independent SourceDirection type is introduced here.
------------------------------------------------------------------------

record SelectedCMP116TermwiseLocalization
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    -- The selected density is the existing T5/RG carrier, not a new
    -- abstract density record.  This coordinate is retained so the source
    -- replay cannot silently detach from the selected carrier.
    selectedT5RGDensity : Set
    selectedT5RGDensityIsBase : selectedT5RGDensity ≡ R318.SourceDirection base

    -- Actual observable-indexed insertions on the existing R318 carrier.
    -- For the canonical R403 constructor this carrier is definitionally
    -- `TestObservable`; keeping the field at the carrier level also lets the
    -- owner remain generic over the already-established R318 interface.
    leftObservable rightObservable : R318.SourceDirection base
    leftJ rightJ : R318.SourceDirection base
    leftJIsObservableIndexed :
      leftJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) leftObservable
    rightJIsObservableIndexed :
      rightJ ≡ Cumulant.sourceDirectionOf (R318.meaning base) rightObservable

    -- The literal CMP116 decoupling boundary is retained as an input
    -- coordinate.  Its admissibility is not inferred from a source label.
    DecouplingBoundaryAssignment : Set
    selectedDecouplingBoundary : DecouplingBoundaryAssignment

    -- One term is the differentiated (1.23) generalized-walk/local-activity
    -- contribution at the selected boundary assignment.
    Term Domain Factor : Set
    localizedDomains : List Domain
    termsWithCommonY : Domain → List Term
    differentiatedTerm : Domain → Term → ℝ
    differentiatedTermMajorant : Domain → Term → ℝ
    commonYBoundaryIntegrand commonYShell : Domain → ℝ
    selectedBoundaryIntegrand selectedConnectingShell : ℝ

    -- Literal source-level finite product carried by each differentiated term.
    -- `beforeFactor` and `afterFactor` are the two neighboring decoupled/local
    -- products; `ordinaryFactorMajorant` bounds either factor, while
    -- `markedFactorMajorant` bounds the one-factor replacement difference.
    termFactors : Domain → Term → List Factor
    beforeFactor afterFactor : Domain → Term → Factor → ℝ
    ordinaryFactorMajorant markedFactorMajorant :
      Domain → Term → Factor → ℝ

    differentiatedTermIsMarkedProductDifference :
      ∀ domain term →
      differentiatedTerm domain term ≡
        Hess.productℝ (beforeFactor domain term) (termFactors domain term)
        -ℝ
        Hess.productℝ (afterFactor domain term) (termFactors domain term)

    differentiatedTermMajorantIsFactorwiseMarkedProduct :
      ∀ domain term →
      differentiatedTermMajorant domain term ≡
        FactorProduct.markedProductMajorant
          (ordinaryFactorMajorant domain term)
          (markedFactorMajorant domain term)
          (termFactors domain term)

    -- These are now the literal source-replay leaves.  Round72 compiles them
    -- into the whole-term majorant; R406 no longer accepts that conclusion as
    -- a separate physical assumption.
    ordinaryFactorMajorantNonnegative :
      ∀ domain term factor →
      0ℝ ≤ℝ ordinaryFactorMajorant domain term factor

    beforeFactorBelowOrdinary :
      ∀ domain term factor →
      absℝ (beforeFactor domain term factor)
        ≤ℝ ordinaryFactorMajorant domain term factor

    afterFactorBelowOrdinary :
      ∀ domain term factor →
      absℝ (afterFactor domain term factor)
        ≤ℝ ordinaryFactorMajorant domain term factor

    markedFactorDifferenceBelow :
      ∀ domain term factor →
      absℝ
        (beforeFactor domain term factor
          -ℝ afterFactor domain term factor)
        ≤ℝ markedFactorMajorant domain term factor

    -- Literal CMP116 source replay: the complete selected boundary is the sum
    -- of common-Y contributions, and each common-Y contribution is the sum of
    -- differentiated terms.
    selectedBoundaryIsCommonYSum :
      selectedBoundaryIntegrand ≡
        Resum.sumℝ commonYBoundaryIntegrand localizedDomains

    commonYBoundaryIsTermSum :
      ∀ domain →
      commonYBoundaryIntegrand domain ≡
        Resum.sumℝ
          (differentiatedTerm domain)
          (termsWithCommonY domain)

    -- Positive CMP116 common-Y shell summation.
    differentiatedMajorantsBelowCommonYShell :
      ∀ domain →
      Resum.sumℝ
        (differentiatedTermMajorant domain)
        (termsWithCommonY domain)
        ≤ℝ commonYShell domain

    -- Positive outer CMP116 localization-domain summation.
    commonYShellsBelowSelectedConnectingShell :
      Resum.sumℝ commonYShell localizedDomains
        ≤ℝ selectedConnectingShell

open SelectedCMP116TermwiseLocalization public

------------------------------------------------------------------------
-- Round72 discharges the whole-term majorant from the literal factor bounds.
------------------------------------------------------------------------

differentiatedTermBelowMajorant :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
  (application : SelectedCMP116TermwiseLocalization base) →
  ∀ domain term →
  absℝ (differentiatedTerm application domain term)
    ≤ℝ differentiatedTermMajorant application domain term
differentiatedTermBelowMajorant application domain term
  rewrite differentiatedTermIsMarkedProductDifference application domain term
        | differentiatedTermMajorantIsFactorwiseMarkedProduct application domain term =
  FactorProduct.markedProductDifferenceFromFactorwiseBounds
    (beforeFactor application domain term)
    (afterFactor application domain term)
    (ordinaryFactorMajorant application domain term)
    (markedFactorMajorant application domain term)
    (termFactors application domain term)
    (ordinaryFactorMajorantNonnegative application domain term)
    (beforeFactorBelowOrdinary application domain term)
    (afterFactorBelowOrdinary application domain term)
    (markedFactorDifferenceBelow application domain term)

------------------------------------------------------------------------
-- The actual theorem-bearing composition consumed by R402.
------------------------------------------------------------------------

commonYLocalizationFromSelectedTermwise :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
  (application : SelectedCMP116TermwiseLocalization base) →
  ∀ domain →
  absℝ (commonYBoundaryIntegrand application domain)
    ≤ℝ commonYShell application domain
commonYLocalizationFromSelectedTermwise application domain =
  R404.cmp116CommonYAbsoluteBoundaryBound
    (termsWithCommonY application domain)
    (differentiatedTerm application domain)
    (differentiatedTermMajorant application domain)
    (commonYBoundaryIntegrand application domain)
    (commonYShell application domain)
    (commonYBoundaryIsTermSum application domain)
    (differentiatedTermBelowMajorant application)
    (differentiatedMajorantsBelowCommonYShell application)

selectedBoundaryLocalizationFromR404R405 :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
  (application : SelectedCMP116TermwiseLocalization base) →
  absℝ (selectedBoundaryIntegrand application)
    ≤ℝ selectedConnectingShell application
selectedBoundaryLocalizationFromR404R405 application =
  R405.cmp116NestedAbsoluteBoundaryLocalization
    (localizedDomains application)
    (commonYBoundaryIntegrand application)
    (commonYShell application)
    (selectedBoundaryIntegrand application)
    (selectedConnectingShell application)
    (selectedBoundaryIsCommonYSum application)
    (commonYLocalizationFromSelectedTermwise application)
    (commonYShellsBelowSelectedConnectingShell application)

------------------------------------------------------------------------
-- Status boundary: the owner is theorem-bearing, but an inhabitant still
-- requires the literal selected CMP99/CMP109/CMP116 factorwise replay above.
-- These booleans are deliberately not used as proof terms.
------------------------------------------------------------------------

round406SourceReplayOwnerWritten : Bool
round406SourceReplayOwnerWritten = true

round406SourceReplayOwnerWrittenIsTrue :
  round406SourceReplayOwnerWritten ≡ true
round406SourceReplayOwnerWrittenIsTrue = refl

round406OpaqueWholeTermMajorantStillPrimitive : Bool
round406OpaqueWholeTermMajorantStillPrimitive = false

round406OpaqueWholeTermMajorantStillPrimitiveIsFalse :
  round406OpaqueWholeTermMajorantStillPrimitive ≡ false
round406OpaqueWholeTermMajorantStillPrimitiveIsFalse = refl

round406FactorwiseSourceBoundsStillProofBearing : Bool
round406FactorwiseSourceBoundsStillProofBearing = true

round406FactorwiseSourceBoundsStillProofBearingIsTrue :
  round406FactorwiseSourceBoundsStillProofBearing ≡ true
round406FactorwiseSourceBoundsStillProofBearingIsTrue = refl

round406ConcreteSelectedSourceReplayObserved : Bool
round406ConcreteSelectedSourceReplayObserved = false

round406ConcreteSelectedSourceReplayObservedIsFalse :
  round406ConcreteSelectedSourceReplayObserved ≡ false
round406ConcreteSelectedSourceReplayObservedIsFalse = refl

round406KernelCertifiedAtCurrentHead : Bool
round406KernelCertifiedAtCurrentHead = false

round406KernelCertifiedAtCurrentHeadIsFalse :
  round406KernelCertifiedAtCurrentHead ≡ false
round406KernelCertifiedAtCurrentHeadIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
