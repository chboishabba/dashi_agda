{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116FirstGradientSharedMarkedExact where

------------------------------------------------------------------------
-- ROUND102 B->C: FIRST GRADIENT REUSES THE SAME CMP116 MARKED ANALYTIC SHELL
--
-- `SharedMarkedAnalyticShellControl` deliberately separates the source-native
-- analytic shell from a particular response projected from it.  Therefore a
-- first field/source derivative needed by the Heat/Doob covariance can reuse
-- the SAME hessian-mark shell whenever Cauchy differentiation identifies that
-- response below `markedAnalyticShell hessianMark`.
--
-- No fourth mark and no new decay constant are needed.  The generic response
-- compiler then gives the same rooted 1/2 shell and weighted partial-row bound.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared
import DASHI.Physics.YangMills.BalabanRootedKPToHessianRowBudgetExact as Hess
import DASHI.Physics.YangMills.BalabanRootedKPToExponentialWeightedHessianExact as Weighted

record CMP116FirstGradientSharedMarkedControl
    (Scale Volume Root : Set) : Set₁ where
  field
    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root

    firstGradientShell : Scale → Volume → Root → Nat → ℚ
    firstGradientShellNonnegative : ∀ scale volume root depth →
      0ℚ ≤ firstGradientShell scale volume root depth

    -- Literal Cauchy/source-coordinate identification.  The hessian mark names
    -- the physical spatial grade; derivative ORDER is not encoded by the mark.
    firstGradientBelowHessianMarkedAnalytic : ∀ scale volume root depth →
      firstGradientShell scale volume root depth
      ≤ Shared.markedAnalyticShell shared Shared.hessianMark scale volume root depth

open CMP116FirstGradientSharedMarkedControl public

firstGradientResponseControl :
  ∀ {Scale Volume Root} →
  CMP116FirstGradientSharedMarkedControl Scale Volume Root →
  Hess.RootedHessianShellControl Scale Volume Root
firstGradientResponseControl dataSet =
  Shared.responseControl
    (shared dataSet)
    Shared.hessianMark
    (firstGradientShell dataSet)
    (firstGradientBelowHessianMarkedAnalytic dataSet)

firstGradientWeightedControl :
  ∀ {Scale Volume Root} →
  CMP116FirstGradientSharedMarkedControl Scale Volume Root →
  Weighted.ExponentialWeightedHessianShellControl Scale Volume Root
firstGradientWeightedControl dataSet = record
  { Weighted.ExponentialWeightedHessianShellControl.hessianControl =
      firstGradientResponseControl dataSet
  }

firstGradientWeightedPartial :
  ∀ {Scale Volume Root} →
  CMP116FirstGradientSharedMarkedControl Scale Volume Root →
  Scale → Volume → Root → Nat → ℚ
firstGradientWeightedPartial dataSet =
  Weighted.weightedHessianPartial (firstGradientWeightedControl dataSet)

firstGradientWeightedPartialBelowSharedConstant :
  ∀ {Scale Volume Root}
    (dataSet : CMP116FirstGradientSharedMarkedControl Scale Volume Root)
    scale volume root depth →
  firstGradientWeightedPartial dataSet scale volume root depth
  ≤ Shared.hessianAnalyticConstant (shared dataSet)
firstGradientWeightedPartialBelowSharedConstant dataSet =
  Weighted.weightedHessianRowUniformlyBelowDerivativeConstant
    (firstGradientWeightedControl dataSet)

cmp116FirstGradientReusesSharedMarkedShellLevel : ProofLevel
cmp116FirstGradientReusesSharedMarkedShellLevel = machineChecked

cmp116FirstGradientWeightedRowLevel : ProofLevel
cmp116FirstGradientWeightedRowLevel = machineChecked

-- CMP116 Sect.1 explicitly states that the localized analytic expressions are
-- differentiated by Cauchy formula and retain the exponential localization.
-- The remaining physical seam is literal identification of the Heat/Doob first
-- derivative with that source coordinate on the already-declared common radius.
literalCMP116FirstGradientCoordinateIdentificationLevel : ProofLevel
literalCMP116FirstGradientCoordinateIdentificationLevel = conditional
