{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116AnchoredPhysicalStaticMajorizationRound263Exact where

------------------------------------------------------------------------
-- ROUND263 / R261 COMPARISON + R260 ANCHOR -> R257 STATIC SHELL PAYMENT
--
-- R261 pays a rational DOMAIN-COMPARISON debt on the literal physical CMP116
-- Hessian once the source-native marked comparison is realized.
-- R260 compiles comparison + reference anchor into an absolute rational debt.
-- Round257, however, consumes the already-canonical rational
-- `hessianInfluenceShell`.
--
-- This file supplies the missing compiler between those surfaces.  The only
-- additional source/application equality is that the exact R260 absolute debt
-- is the SAME rational Hessian shell used by Round257.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _+ℝ_; _-ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP109116LiteralDifferentiatedCarrierRound103Exact as Carrier
import DASHI.Physics.YangMills.BalabanCMP116PhysicalDecoupledComparisonRound261Exact as Comparison
import DASHI.Physics.YangMills.BalabanCMP116AnchoredHessianMajorantRound260Exact as Anchor
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanA2RationalShellBudgetToRealRound108Exact as Embed
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact as Shared

record AnchoredPhysicalStaticShell
    {carrier : Carrier.LiteralDifferentiatedEffectiveDensityCarrier}
    {D : Decoupled.DecoupledActivityHessianData}
    (comparison : Comparison.CMP116PhysicalDecoupledComparison
      {carrier = carrier} D)
    (embedding : Embed.OrderedRationalRealRingEmbedding)
    (Scale Volume Root : Set) : Set₁ where
  field
    rationalizedComparison :
      Comparison.RationalizedCMP116PhysicalComparison comparison embedding

    shared : Shared.SharedMarkedAnalyticShellControl Scale Volume Root
    scale : Scale
    volume : Volume
    root : Root
    depth : Nat

    referenceDebt : ℚ
    referenceDebtNonnegative : ℚ.0ℚ ≤ referenceDebt

    referenceAbsoluteBound :
      absℝ
        (Carrier.cmp116PhysicalMarkedHessian carrier
          (Comparison.referenceBackground comparison)
          (Comparison.physicalU comparison)
          (Comparison.physicalV comparison))
      ≤ℝ Embed.embed embedding referenceDebt

    -- Standard additive recomposition on the literal physical Hessian carrier.
    selectedIsComparisonPlusReference :
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.selectedBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
      ≡
      (Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.selectedBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
       -ℝ
       Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.referenceBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison))
      +ℝ
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.referenceBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)

    -- SAME rational consumer identity.  This is the actual source-to-Row-C
    -- payment: comparison debt + reference debt is not merely <= some nearby
    -- shell; it is identified with the exact hessianInfluenceShell consumed by
    -- Round257.
    absoluteDebtIsHessianInfluenceShell :
      Comparison.comparisonDebt rationalizedComparison + referenceDebt
      ≡
      Shared.hessianInfluenceShell shared scale volume root depth

open AnchoredPhysicalStaticShell public

asRound260AnchoredMajorant :
  ∀ {carrier D embedding Scale Volume Root}
    {comparison : Comparison.CMP116PhysicalDecoupledComparison
      {carrier = carrier} D} →
  (dataSet : AnchoredPhysicalStaticShell
    comparison embedding Scale Volume Root) →
  Anchor.AnchoredRealHessianMajorant embedding
asRound260AnchoredMajorant {carrier} {comparison = comparison} dataSet = record
  { Anchor.AnchoredRealHessianMajorant.selected =
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.selectedBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
  ; Anchor.AnchoredRealHessianMajorant.comparison =
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.selectedBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
      -ℝ
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.referenceBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
  ; Anchor.AnchoredRealHessianMajorant.reference =
      Carrier.cmp116PhysicalMarkedHessian carrier
        (Comparison.referenceBackground comparison)
        (Comparison.physicalU comparison)
        (Comparison.physicalV comparison)
  ; Anchor.AnchoredRealHessianMajorant.comparisonDebt =
      Comparison.comparisonDebt (rationalizedComparison dataSet)
  ; Anchor.AnchoredRealHessianMajorant.referenceDebt = referenceDebt dataSet
  ; Anchor.AnchoredRealHessianMajorant.comparisonDebtNonnegative =
      Comparison.comparisonDebtNonnegative (rationalizedComparison dataSet)
  ; Anchor.AnchoredRealHessianMajorant.referenceDebtNonnegative =
      referenceDebtNonnegative dataSet
  ; Anchor.AnchoredRealHessianMajorant.selectedIsComparisonPlusReference =
      selectedIsComparisonPlusReference dataSet
  ; Anchor.AnchoredRealHessianMajorant.comparisonAbsMajorized =
      Comparison.physicalComparisonRationalMajorized
        (rationalizedComparison dataSet)
  ; Anchor.AnchoredRealHessianMajorant.referenceAbsMajorized =
      referenceAbsoluteBound dataSet
  }

physicalStaticHessianMajorizedByExactRowCShell :
  ∀ {carrier D embedding Scale Volume Root}
    {comparison : Comparison.CMP116PhysicalDecoupledComparison
      {carrier = carrier} D} →
  (dataSet : AnchoredPhysicalStaticShell
    comparison embedding Scale Volume Root) →
  absℝ
    (Carrier.cmp116PhysicalMarkedHessian carrier
      (Comparison.selectedBackground comparison)
      (Comparison.physicalU comparison)
      (Comparison.physicalV comparison))
  ≤ℝ
  Embed.embed embedding
    (Shared.hessianInfluenceShell
      (shared dataSet)
      (scale dataSet)
      (volume dataSet)
      (root dataSet)
      (depth dataSet))
physicalStaticHessianMajorizedByExactRowCShell
    {embedding = embedding} dataSet =
  subst
    (λ debt →
      absℝ
        (Anchor.selected (asRound260AnchoredMajorant dataSet))
      ≤ℝ Embed.embed embedding debt)
    (absoluteDebtIsHessianInfluenceShell dataSet)
    (Anchor.selectedAbsMajorized (asRound260AnchoredMajorant dataSet))

------------------------------------------------------------------------
-- Status / boundary.
------------------------------------------------------------------------

anchoredPhysicalStaticShellCompilerLevel : ProofLevel
anchoredPhysicalStaticShellCompilerLevel = machineChecked

referenceAnchorSourcePaymentLevel : ProofLevel
referenceAnchorSourcePaymentLevel = conditional

absoluteDebtExactHessianShellIdentificationLevel : ProofLevel
absoluteDebtExactHessianShellIdentificationLevel = conditional

record AnchoredPhysicalStaticBoundary263 : Set where
  constructor anchored-physical-static-boundary263
  field
    R261ComparisonReused : Set
    R260AnchorCompilerReused : Set
    Round257ExactShellTargetReused : Set
    referenceAnchorStillSourceFacing : Set
    exactDebtShellIdentityStillSourceFacing : Set

canonicalAnchoredPhysicalStaticBoundary263 : AnchoredPhysicalStaticBoundary263
canonicalAnchoredPhysicalStaticBoundary263 = record
  { R261ComparisonReused = ℚ
  ; R260AnchorCompilerReused = ℚ
  ; Round257ExactShellTargetReused = ℚ
  ; referenceAnchorStillSourceFacing = ℚ
  ; exactDebtShellIdentityStillSourceFacing = ℚ
  }
