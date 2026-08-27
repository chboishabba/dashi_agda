module DASHI.Governance.SafeJustFeministClimateJusticeBoundaryExact where

open import DASHI.Core.Prelude
import DASHI.Governance.FeministClimateJusticeSourceRegistryExact as Sources
import DASHI.Governance.WaringProductionBoundaryNonfactorabilityExact as WaringGeneric
import DASHI.Governance.FeministClimateJusticeResidualBundleExact as ResidualGeneric

------------------------------------------------------------------------
-- FEMINIST ECONOMICS / FEMINIST CLIMATE JUSTICE COMPATIBILITY BOUNDARY
--
-- This file predates the stronger generic/source-specific tranche and is kept as
-- a compact compatibility surface for existing #625 regression names.  Generic
-- theorem ownership now lives in:
--
--   Core/MeasurementBoundaryNonfactorabilityExact
--   Core/ResponsibilityBurdenNonfactorabilityExact
--   Core/PoliticalContestabilityExact
--   Core/CategoryAuthorityAuditExact
--   Core/MultiaxialResidualBundleExact
--
-- and the source-specific bridges under Governance.
--
-- Source identifiers are owned by FeministClimateJusticeSourceRegistryExact.
-- In particular, Kathryn Yusoff's 2018 book is cited by verified ISBN
-- 9781517907532 (paperback) / 9781452961057 (eBook); NO DOI is asserted here.
------------------------------------------------------------------------

data FeministClimateSource : Set where
  power2004 waring1988 macgregor2014 sultana2022
  alstonFullerKwarney2023 carterHoward2020 yusoff2018 maathai2004
  : FeministClimateSource

data SourceRole : Set where
  socialProvisioningMethodology
  productionBoundaryCritique
  postPoliticalAuthorityCritique
  climateColoniality
  situatedLivedOutcome
  hiddenNegotiatingContribution
  categoryNeutralityCritique
  bottomUpSituatedAuthority
  : SourceRole

record SourceRoleEntry : Set where
  constructor sourceRoleEntry
  field
    source : FeministClimateSource
    role : SourceRole

powerProvisioningRole : SourceRoleEntry
powerProvisioningRole = sourceRoleEntry power2004 socialProvisioningMethodology

waringRole : SourceRoleEntry
waringRole = sourceRoleEntry waring1988 productionBoundaryCritique

macgregorPostPoliticalRole : SourceRoleEntry
macgregorPostPoliticalRole = sourceRoleEntry macgregor2014 postPoliticalAuthorityCritique

sultanaRole : SourceRoleEntry
sultanaRole = sourceRoleEntry sultana2022 climateColoniality

yusoffRole : SourceRoleEntry
yusoffRole = sourceRoleEntry yusoff2018 categoryNeutralityCritique

maathaiRole : SourceRoleEntry
maathaiRole = sourceRoleEntry maathai2004 bottomUpSituatedAuthority

verifiedPowerSource : Sources.SourceReference
verifiedPowerSource = Sources.power2004

verifiedWaringSource : Sources.SourceReference
verifiedWaringSource = Sources.waring1988

verifiedMacGregorSource : Sources.SourceReference
verifiedMacGregorSource = Sources.macGregor2014

verifiedSultanaSource : Sources.SourceReference
verifiedSultanaSource = Sources.sultana2022

verifiedYusoffSource : Sources.SourceReference
verifiedYusoffSource = Sources.yusoff2018

------------------------------------------------------------------------
-- Legacy finite Waring shadow retained for compatibility.
-- The theorem-bearing factorization obstruction is now owned by
-- WaringProductionBoundaryNonfactorabilityExact.
------------------------------------------------------------------------

data ActivityState : Set where
  noActivity unpaidCare paidMarketActivity : ActivityState

countedOutput : ActivityState → Nat
countedOutput noActivity = 0
countedOutput unpaidCare = 0
countedOutput paidMarketActivity = 1

provisioningContribution : ActivityState → Nat
provisioningContribution noActivity = 0
provisioningContribution unpaidCare = 1
provisioningContribution paidMarketActivity = 1

sameCountedOutput : countedOutput noActivity ≡ countedOutput unpaidCare
sameCountedOutput = refl

countedOutputDoesNotRecoverProvisioning :
  provisioningContribution noActivity ≡ provisioningContribution unpaidCare → ⊥
countedOutputDoesNotRecoverProvisioning ()

strongWaringNonfactorabilityAvailable :
  DASHI.Core.ConsumerDescentMinimalObserverExact.FactorsThrough
    WaringGeneric.accountObserver WaringGeneric.provisioningContribution → ⊥
strongWaringNonfactorabilityAvailable =
  WaringGeneric.provisioningDoesNotDescendThroughAccountingBoundary

------------------------------------------------------------------------
-- Legacy residual-kind names retained for regression compatibility.  The full
-- five-coordinate residual contract is owned by FeministClimateJusticeResidualBundleExact.
------------------------------------------------------------------------

data ResidualKind : Set where
  phenomenonResidual epistemicResidual responsibilityImpactAsymmetryResidual
  categoricalAuthorityResidual democraticAuthorityResidual : ResidualKind

phenomenonResidualDiffersFromEpistemicResidual :
  phenomenonResidual ≡ epistemicResidual → ⊥
phenomenonResidualDiffersFromEpistemicResidual ()

responsibilityResidualDiffersFromDataResidual :
  responsibilityImpactAsymmetryResidual ≡ epistemicResidual → ⊥
responsibilityResidualDiffersFromDataResidual ()

categoricalAuthorityResidualDiffersFromMissingData :
  categoricalAuthorityResidual ≡ epistemicResidual → ⊥
categoricalAuthorityResidualDiffersFromMissingData ()

fiveAxisResidualBundleAvailable : ResidualGeneric.ClimateJusticeResidualBundle
fiveAxisResidualBundleAvailable = ResidualGeneric.canonicalClimateJusticeResiduals

record FeministClimateJusticeBoundary : Set where
  constructor feministClimateJusticeBoundary
  field
    marketExchangeExhaustsSocialProvisioning : Bool
    marketExchangeExhaustsSocialProvisioningIsFalse :
      marketExchangeExhaustsSocialProvisioning ≡ false
    countedEconomicOutputExhaustsProvisioning : Bool
    countedEconomicOutputExhaustsProvisioningIsFalse :
      countedEconomicOutputExhaustsProvisioning ≡ false
    completeIndicatorCoverageCertifiesParticipatoryJustice : Bool
    completeIndicatorCoverageCertifiesParticipatoryJusticeIsFalse :
      completeIndicatorCoverageCertifiesParticipatoryJustice ≡ false
    technicallyQualifiedForecastAuthorizesDepoliticizedAdministration : Bool
    technicallyQualifiedForecastAuthorizesDepoliticizedAdministrationIsFalse :
      technicallyQualifiedForecastAuthorizesDepoliticizedAdministration ≡ false
    completeDataLedgerDischargesResponsibilityImpactAsymmetry : Bool
    completeDataLedgerDischargesResponsibilityImpactAsymmetryIsFalse :
      completeDataLedgerDischargesResponsibilityImpactAsymmetry ≡ false
    completeDataLedgerCertifiesCategoryNeutrality : Bool
    completeDataLedgerCertifiesCategoryNeutralityIsFalse :
      completeDataLedgerCertifiesCategoryNeutrality ≡ false
    formalDelegationVisibilityRecoversActualNegotiatingContribution : Bool
    formalDelegationVisibilityRecoversActualNegotiatingContributionIsFalse :
      formalDelegationVisibilityRecoversActualNegotiatingContribution ≡ false
    ecologicalFunctioningAutomaticallyCreatesDemocraticAuthority : Bool
    ecologicalFunctioningAutomaticallyCreatesDemocraticAuthorityIsFalse :
      ecologicalFunctioningAutomaticallyCreatesDemocraticAuthority ≡ false

canonicalFeministClimateJusticeBoundary : FeministClimateJusticeBoundary
canonicalFeministClimateJusticeBoundary =
  feministClimateJusticeBoundary
    false refl false refl false refl false refl false refl false refl false refl false refl
