{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound323Exact where

------------------------------------------------------------------------
-- ROUND323 / CURRENT B DEBT-KIND NORMALIZATION
--
-- R317's five coordinates are all required by the literal consumer-facing
-- construction, but they are not five equal analytic theorems.
--
--   H1  selected two-J magnitude localization
--       = the one B-side quantitative clustering producer;
--
--   H2a physical Euclidean-time/support semantics
--   H2b selected Wilson-cylinder / observable-algebra presentation
--   H3  same-Hamiltonian transfer-energy / decay-ratio coordinate
--       = same-object/application debts;
--
--   H2c upper-order closure for the selected scalar convergence
--       = topology/analysis-authority debt.
--
-- R320 minimizes H1 to one selected-carrier marked-source estimate.  R322 then
-- separates the already-published CMP116 differentiated J-localization theorem
-- from the physical statement that the selected T5 source directions lie in its
-- declared analytic J domain.  This round does not demote any of R317's five
-- consumer coordinates; it only stops proof search from counting all five as
-- fresh Yang--Mills analytic estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Interop.IntrospectiveProofLoopExact as Introspective
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound317Exact as R317
import DASHI.Physics.YangMills.BalabanClayCanonicalBFrontierRound320Exact as R320
import DASHI.Physics.YangMills.BalabanCMP116SelectedJDomainApplicationRound322Exact as R322

-- Local debt kind supplements, rather than replaces, the generic consumer role.
data BDebtKind323 : Set where
  analyticProducerDebt : BDebtKind323
  sameObjectApplicationDebt : BDebtKind323
  topologyAuthorityDebt : BDebtKind323

data CanonicalBCoordinate323 : Set where
  h1SelectedTwoJLocalization : CanonicalBCoordinate323
  h2aPhysicalTimeSupport : CanonicalBCoordinate323
  h2bSelectedWilsonPresentation : CanonicalBCoordinate323
  h2cScalarOrderClosure : CanonicalBCoordinate323
  h3TransferEnergyDecayCoordinate : CanonicalBCoordinate323

searchRole323 : CanonicalBCoordinate323 → Introspective.ProofSearchTargetRole
searchRole323 h1SelectedTwoJLocalization = Introspective.canonicalConsumerResidual
searchRole323 h2aPhysicalTimeSupport = Introspective.canonicalConsumerResidual
searchRole323 h2bSelectedWilsonPresentation = Introspective.canonicalConsumerResidual
searchRole323 h2cScalarOrderClosure = Introspective.canonicalConsumerResidual
searchRole323 h3TransferEnergyDecayCoordinate = Introspective.canonicalConsumerResidual

debtKind323 : CanonicalBCoordinate323 → BDebtKind323
debtKind323 h1SelectedTwoJLocalization = analyticProducerDebt
debtKind323 h2aPhysicalTimeSupport = sameObjectApplicationDebt
debtKind323 h2bSelectedWilsonPresentation = sameObjectApplicationDebt
debtKind323 h2cScalarOrderClosure = topologyAuthorityDebt
debtKind323 h3TransferEnergyDecayCoordinate = sameObjectApplicationDebt

record Round323Boundary : Set where
  constructor round323-boundary
  field
    canonicalConsumerStillHasFiveCoordinates : Bool
    canonicalConsumerStillHasFiveCoordinatesIsTrue :
      canonicalConsumerStillHasFiveCoordinates ≡ true

    fiveCoordinatesAreFiveFreshYMAnalyticTheorems : Bool
    fiveCoordinatesAreFiveFreshYMAnalyticTheoremsIsFalse :
      fiveCoordinatesAreFiveFreshYMAnalyticTheorems ≡ false

    h1IsOnlyCurrentBAnalyticProducerDebt : Bool
    h1IsOnlyCurrentBAnalyticProducerDebtIsTrue :
      h1IsOnlyCurrentBAnalyticProducerDebt ≡ true

    h2aIsSameObjectApplicationDebt : Bool
    h2aIsSameObjectApplicationDebtIsTrue :
      h2aIsSameObjectApplicationDebt ≡ true

    h2bIsSameObjectApplicationDebt : Bool
    h2bIsSameObjectApplicationDebtIsTrue :
      h2bIsSameObjectApplicationDebt ≡ true

    h2cIsTopologyAuthorityDebt : Bool
    h2cIsTopologyAuthorityDebtIsTrue :
      h2cIsTopologyAuthorityDebt ≡ true

    h3IsSameObjectApplicationDebt : Bool
    h3IsSameObjectApplicationDebtIsTrue :
      h3IsSameObjectApplicationDebt ≡ true

    cmp116DifferentiatedJLocalizationNeedsReproof : Bool
    cmp116DifferentiatedJLocalizationNeedsReproofIsFalse :
      cmp116DifferentiatedJLocalizationNeedsReproof ≡ false

    selectedJDomainApplicabilityStillOpen : Bool
    selectedJDomainApplicabilityStillOpenIsTrue :
      selectedJDomainApplicabilityStillOpen ≡ true

canonicalRound323Boundary : Round323Boundary
canonicalRound323Boundary =
  round323-boundary
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl

-- Preserve the authoritative R317 consumer levels.
round323H1Level : ProofLevel
round323H1Level = R317.round317H1SelectedTwoJMagnitudeLocalizationLevel

round323H2aLevel : ProofLevel
round323H2aLevel = R317.round317H2aPhysicalTimeSupportSemanticsLevel

round323H2bLevel : ProofLevel
round323H2bLevel = R317.round317H2bSelectedWilsonPresentationLevel

round323H2cLevel : ProofLevel
round323H2cLevel = R317.round317H2cScalarOrderClosureLevel

round323H3Level : ProofLevel
round323H3Level = R317.round317H3TransferEnergyDecayCoordinateLevel

-- Preferred H1 producer decomposition after R320/R322.
round323PreferredH1ProducerLevel : ProofLevel
round323PreferredH1ProducerLevel = R320.round320PreferredSelectedMarkedDecayLevel

round323CMP116SourceLocalizationLevel : ProofLevel
round323CMP116SourceLocalizationLevel = R322.cmp116DifferentiatedLocalizationSourceLevel

round323SelectedJDomainApplicabilityLevel : ProofLevel
round323SelectedJDomainApplicabilityLevel = R322.selectedJDomainApplicabilityLevel

round323CompilerLevel : ProofLevel
round323CompilerLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
