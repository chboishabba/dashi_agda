{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109SelectedT5SameObjectRound321Exact where

------------------------------------------------------------------------
-- ROUND321 / CMP109 E^(2)/Pi -> SELECTED T5 SECOND-DERIVATIVE SAME-OBJECT WELD
--
-- R320 minimized the preferred H1 producer to one theorem on the exact selected
-- T5 carrier.  Source archaeology sharpens that theorem further without
-- changing the canonical B consumer:
--
--   (A) CMP109/CMP116 source payment:
--       the differentiated E^(2)/Pi response has the selected rooted-shell
--       exponential bound;
--
--   (B) same-object payment:
--       that source response magnitude is literally the selected normalized
--       mixed-log-partition second derivative magnitude.
--
-- Their composition constructs the R320 direct selected decay payment.  This
-- owner does not claim either source instantiation or the same-object weld.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _≤_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.NormalizedTwoSourceConnectedCumulantExact as Cumulant
import DASHI.Physics.YangMills.BalabanClayT2TraversalRootedShellExact as Shell
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanT5DirectSelectedMarkedDecayRound320Exact as R320
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as CMP109

record PublishedCMP109SelectedShellPayment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    : Set₁ where
  field
    sourceE2PiMagnitude :
      Nat → TestObservable → TestObservable → ℚ

    sourceE2PiMagnitudeBelowSelectedShell :
      ∀ cutoff left right →
      sourceE2PiMagnitude cutoff left right
      ≤ Shell.rootedShell (R318.shellData base)
          (R318.scaleOf base cutoff)
          (R318.volumeOf base cutoff)
          (R318.connectingRoot base cutoff left right)
          (R318.physicalDistance base left right)

open PublishedCMP109SelectedShellPayment public

record SelectedT5CMP109SameObject
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    (base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension)
    (source : PublishedCMP109SelectedShellPayment base)
    : Set₁ where
  field
    selectedMixedDerivativeMagnitudeIsSourceE2Pi :
      ∀ cutoff left right →
      R278.magnitude extension
        (Cumulant.mixedSecondLogDerivative (R318.calculus base)
          left right cutoff)
      ≡ sourceE2PiMagnitude source cutoff left right

open SelectedT5CMP109SameObject public

cmp109SameObjectBuildsR320Payment :
  ∀ {Measure TestObservable}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    {source : PublishedCMP109SelectedShellPayment base} →
  SelectedT5CMP109SameObject base source →
  R320.DirectSelectedT5MarkedDecayPayment base
cmp109SameObjectBuildsR320Payment {extension = extension} {base = base}
    {source = source} weld = record
  { R320.DirectSelectedT5MarkedDecayPayment.mixedDerivativeMagnitudeBelowSelectedShell =
      λ cutoff left right →
        subst
          (λ lower →
            lower ≤ Shell.rootedShell (R318.shellData base)
              (R318.scaleOf base cutoff)
              (R318.volumeOf base cutoff)
              (R318.connectingRoot base cutoff left right)
              (R318.physicalDistance base left right))
          (sym (selectedMixedDerivativeMagnitudeIsSourceE2Pi
            weld cutoff left right))
          (sourceE2PiMagnitudeBelowSelectedShell source cutoff left right)
  }

------------------------------------------------------------------------
-- Proof-search classification.
------------------------------------------------------------------------

cmp109DifferentiatedDecayIsNewYMAnalysis : Bool
cmp109DifferentiatedDecayIsNewYMAnalysis = false

selectedT5CMP109IdentityIsRepresentationWeld : Bool
selectedT5CMP109IdentityIsRepresentationWeld = true

r320OneFieldCanBeCompiledFromSourcePlusWeld : Bool
r320OneFieldCanBeCompiledFromSourcePlusWeld = true

sourceMetadataAlonePaysSelectedT5H1 : Bool
sourceMetadataAlonePaysSelectedT5H1 = false

clayPromotion : Bool
clayPromotion = false

cmp109DifferentiatedDecayIsNewYMAnalysisIsFalse :
  cmp109DifferentiatedDecayIsNewYMAnalysis ≡ false
cmp109DifferentiatedDecayIsNewYMAnalysisIsFalse = refl

selectedT5CMP109IdentityIsRepresentationWeldIsTrue :
  selectedT5CMP109IdentityIsRepresentationWeld ≡ true
selectedT5CMP109IdentityIsRepresentationWeldIsTrue = refl

r320OneFieldCanBeCompiledFromSourcePlusWeldIsTrue :
  r320OneFieldCanBeCompiledFromSourcePlusWeld ≡ true
r320OneFieldCanBeCompiledFromSourcePlusWeldIsTrue = refl

sourceMetadataAlonePaysSelectedT5H1IsFalse :
  sourceMetadataAlonePaysSelectedT5H1 ≡ false
sourceMetadataAlonePaysSelectedT5H1IsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl

cmp109PublishedDifferentiatedDecayLevel : ProofLevel
cmp109PublishedDifferentiatedDecayLevel = CMP109.cmp109DifferentiatedMarkedActivityDecayLevel

selectedT5CMP109SameObjectLevel : ProofLevel
selectedT5CMP109SameObjectLevel = conditional

round321CompilerLevel : ProofLevel
round321CompilerLevel = machineChecked
