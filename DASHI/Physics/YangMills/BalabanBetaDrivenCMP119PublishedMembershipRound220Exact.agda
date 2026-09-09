{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanBetaDrivenCMP119PublishedMembershipRound220Exact where

------------------------------------------------------------------------
-- ROUND220 / LEAST-PRIVILEGE CMP119 -> CMP122 PUBLISHED MEMBERSHIP
--
-- `SourceNativePublishedFlow` also carries a coarse CMP109 differentiated
-- coordinate because older strong-state consumers wanted E2/Pi immediately.
-- CMP122 Section-2 membership does not consume that coordinate.
--
-- On the preferred route we therefore use only:
--
--   beta-driven complete-density flow
--   + literal CMP119 residual family
--   + the imported CMP122 Theorem-1 witness.
--
-- The complete density built in Round219 has rho_k definitionally equal to the
-- beta-driven flow density, so Theorem 1 applies without a source-state equality
-- or differentiated E2/Pi package.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Beta
import DASHI.Physics.YangMills.Balaban1989Theorem1UVStabilityExact as Published
import DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact as CMP119
import DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact as R219

record BetaDrivenCMP119PublishedResidual
    {trajectory split}
    (inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}) : Set₂ where
  field
    residual : R219.BetaDrivenCMP119ResidualFamily inputs
    theorem1 :
      Published.Balaban1989Theorem1Witness
        (Beta.betaDrivenCompleteDensityFlow inputs)

open BetaDrivenCMP119PublishedResidual public

record PublishedSection2At
    {trajectory split}
    {inputs : Beta.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split}}
    (dataSet : BetaDrivenCMP119PublishedResidual inputs)
    (scale : Nat) : Set₁ where
  field
    sourceForm :
      Published.InSection2DensityClass
        (Beta.betaDrivenCompleteDensityFlow inputs) scale
        (CMP119.rho (R219.completeDensityAt (residual dataSet) scale))

    sourceBounds :
      Published.Section2ConditionsAndBounds
        (Beta.betaDrivenCompleteDensityFlow inputs) scale
        (CMP119.rho (R219.completeDensityAt (residual dataSet) scale))

open PublishedSection2At public

publishedSection2At :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenCMP119PublishedResidual
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale → PublishedSection2At dataSet scale
publishedSection2At dataSet scale = record
  { PublishedSection2At.sourceForm =
      Published.effectiveDensitiesPreserveSection2Form (theorem1 dataSet) scale
  ; PublishedSection2At.sourceBounds =
      Published.effectiveDensitiesSatisfySection2Bounds (theorem1 dataSet) scale
  }

cmp119PublishedDensityIsBetaDensity :
  ∀ {trajectory split inputs}
    (dataSet : BetaDrivenCMP119PublishedResidual
      {trajectory = trajectory} {split = split} inputs) →
  ∀ scale →
  CMP119.rho (R219.completeDensityAt (residual dataSet) scale)
  ≡ Beta.densityAt inputs scale
cmp119PublishedDensityIsBetaDensity dataSet scale = Agda.Builtin.Equality.refl

betaDrivenCMP119PublishedMembershipCompilerLevel : ProofLevel
betaDrivenCMP119PublishedMembershipCompilerLevel = machineChecked

-- This is imported source authority, not a newly proved Clay analytic estimate.
cmp122Theorem1AuthorityLevel : ProofLevel
cmp122Theorem1AuthorityLevel = Published.balaban1989Theorem1SourceLevel

-- Preferred physical/source realization remaining before this compiler fires:
-- the literal CMP119 residual family itself.  The coarse source-native E2/Pi
-- coordinate is no longer a prerequisite of published Section-2 membership.
literalBetaDrivenCMP119PublishedResidualLevel : ProofLevel
literalBetaDrivenCMP119PublishedResidualLevel = conditional
