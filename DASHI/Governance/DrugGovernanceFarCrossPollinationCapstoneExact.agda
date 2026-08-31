module DASHI.Governance.DrugGovernanceFarCrossPollinationCapstoneExact where

open import DASHI.Core.Prelude

import DASHI.Governance.DrugGovernanceFiveProbeWorldExact as Five
import DASHI.Governance.DrugGovernanceFiveProbeOptionConeExact as Cone
import DASHI.Governance.DrugGovernanceFiveProbeAdaptivePlannerExact as Planner
import DASHI.Governance.DrugCategoryCostedQuotientDiscriminatorExact as Costed
import DASHI.Governance.DrugCategoryPhilosophyOperatorAtlasExact as Philosophy
import DASHI.Governance.ObserverValuationAuthoritySeparationExact as Authority
import DASHI.Governance.HistoryObserverAuthorityOptionConeCapstoneExact as HistoryAuthority
import DASHI.Governance.IndigenousAuthorityEnvelopeExact as Indigenous
import DASHI.Governance.SocioTechnicalPowerSelectionAssayExact as Power
import DASHI.Culture.IntersectionalPowerValueFolkModelBoundary as Intersectional

------------------------------------------------------------------------
-- FAR CROSS-POLLINATION CAPSTONE
--
-- Philosophical/feminist/political-economy operators seed candidate probes;
-- discriminator evidence decides whether a probe actually separates the current
-- live fibre.  Option-cone and authority owners then evaluate what the exposed
-- coordinate changes operationally.  No audit lane is promoted to empirical
-- proof authority.
------------------------------------------------------------------------

data AuditTargetsProbe :
  Philosophy.DrugCategoryAudit → Costed.ProbeKind → Set where
  wittgensteinTargetsSubject :
    AuditTargetsProbe Philosophy.wittgensteinUseAudit Costed.subjectProbe
  zizekTargetsHistory :
    AuditTargetsProbe Philosophy.zizekClosureFantasyAudit Costed.historyProbe
  foucaultTargetsAuthority :
    AuditTargetsProbe Philosophy.foucaultPowerClassificationAudit Costed.authorityProbe
  marxTargetsMaterial :
    AuditTargetsProbe Philosophy.marxMaterialInterestAudit Costed.materialBenefitProbe
  nietzscheTargetsHistory :
    AuditTargetsProbe Philosophy.nietzscheValuationFormationAudit Costed.historyProbe
  spinozaTargetsMaterialCapability :
    AuditTargetsProbe Philosophy.spinozaPowerToActAudit Costed.materialBenefitProbe
  kantTargetsAuthority :
    AuditTargetsProbe Philosophy.kantNonInstrumentalisationAudit Costed.authorityProbe
  levinasTargetsSubject :
    AuditTargetsProbe Philosophy.levinasOtherExceedsChartAudit Costed.subjectProbe
  derridaTargetsHistory :
    AuditTargetsProbe Philosophy.derridaNoFinalClosureAudit Costed.historyProbe
  feministTargetsSubject :
    AuditTargetsProbe Philosophy.feministSubjectPositionAudit Costed.subjectProbe
  intersectionalTargetsAuthority :
    AuditTargetsProbe Philosophy.intersectionalAxisAudit Costed.authorityProbe

------------------------------------------------------------------------
-- Sovereignty is not reduced to a philosopher audit.  It is independently
-- sourced by the Indigenous authority envelope and gets its own probe route.
------------------------------------------------------------------------

data SovereigntyProbeAuthority : Set where
  indigenousAuthorityEnvelopeRoutesSovereigntyProbe : SovereigntyProbeAuthority

indigenousBoundary : Indigenous.IndigenousAuthorityEnvelopeBoundary
indigenousBoundary = Indigenous.canonicalIndigenousAuthorityEnvelopeBoundary

------------------------------------------------------------------------
-- Live proof-bearing probes from the expanded world.
------------------------------------------------------------------------

authorityProbeActuallySeparates = Five.authoritySeparates
materialProbeActuallySeparates = Five.materialSeparates
sovereigntyProbeActuallySeparates = Five.sovereigntySeparates

benefitSharingIsReachableInSharedWorld :
  Cone.Available Five.sharedBenefitWorld Cone.benefitSharingClaim
benefitSharingIsReachableInSharedWorld = Cone.sharedBenefitCarriesExtraOption

sovereignGovernanceIsLostByExternalisation :
  Cone.Available Five.baseExternalWorld Cone.sovereignCeremonialGovernance → ⊥
sovereignGovernanceIsLostByExternalisation = Cone.baseLacksSovereignGovernance

------------------------------------------------------------------------
-- Wider canonical boundaries retained directly.
------------------------------------------------------------------------

authoritySeparationBoundary : Authority.ObserverValuationAuthorityBoundary
authoritySeparationBoundary = Authority.canonicalObserverValuationAuthorityBoundary

historyAuthorityBoundary : HistoryAuthority.HistoryObserverAuthorityCapstoneBoundary
historyAuthorityBoundary = HistoryAuthority.canonicalHistoryObserverAuthorityCapstoneBoundary

powerBoundary : Power.SocioTechnicalPowerSelectionBoundary
powerBoundary = Power.canonicalSocioTechnicalPowerSelectionBoundary

intersectionalBoundary : Intersectional.IntersectionalPowerValueFolkModelBoundary
intersectionalBoundary = Intersectional.canonicalIntersectionalPowerValueFolkModelBoundary

plannerBoundary : Planner.FiveProbeAdaptivePlannerBoundary
plannerBoundary = Planner.canonicalFiveProbeAdaptivePlannerBoundary

------------------------------------------------------------------------
-- Non-promotion barriers.
------------------------------------------------------------------------

data AuditTargetingPromotesSeparator : Set where

data SeparatorPromotesCausalMechanism : Set where

data OptionConeDifferencePromotesNormativeVerdict : Set where

data AuthorityProbePromotesMandate : Set where

data MaterialProbePromotesMarxianCause : Set where

data SovereigntyProbePromotesClinicalEfficacy : Set where

auditTargetingDoesNotPromoteSeparator : AuditTargetingPromotesSeparator → ⊥
auditTargetingDoesNotPromoteSeparator ()

separatorDoesNotPromoteCausalMechanism : SeparatorPromotesCausalMechanism → ⊥
separatorDoesNotPromoteCausalMechanism ()

optionConeDifferenceDoesNotPromoteNormativeVerdict : OptionConeDifferencePromotesNormativeVerdict → ⊥
optionConeDifferenceDoesNotPromoteNormativeVerdict ()

authorityProbeDoesNotPromoteMandate : AuthorityProbePromotesMandate → ⊥
authorityProbeDoesNotPromoteMandate ()

materialProbeDoesNotPromoteMarxianCause : MaterialProbePromotesMarxianCause → ⊥
materialProbeDoesNotPromoteMarxianCause ()

sovereigntyProbeDoesNotPromoteClinicalEfficacy : SovereigntyProbePromotesClinicalEfficacy → ⊥
sovereigntyProbeDoesNotPromoteClinicalEfficacy ()

record DrugGovernanceFarCrossPollinationBoundary : Set where
  constructor drugGovernanceFarCrossPollinationBoundary
  field
    philosophyCanSeedProbeSelection : Bool
    philosophyCanSeedProbeSelectionIsTrue : philosophyCanSeedProbeSelection ≡ true
    philosophicalAuditIsEmpiricalSeparatorByItself : Bool
    philosophicalAuditIsEmpiricalSeparatorByItselfIsFalse : philosophicalAuditIsEmpiricalSeparatorByItself ≡ false
    allFiveProbeFamiliesNowHaveLiveSeparatorFixtures : Bool
    allFiveProbeFamiliesNowHaveLiveSeparatorFixturesIsTrue : allFiveProbeFamiliesNowHaveLiveSeparatorFixtures ≡ true
    optionConeCanOperationaliseFineCoordinateDifference : Bool
    optionConeCanOperationaliseFineCoordinateDifferenceIsTrue : optionConeCanOperationaliseFineCoordinateDifference ≡ true
    observationValuationModificationAndMandateRemainSeparate : Bool
    observationValuationModificationAndMandateRemainSeparateIsTrue : observationValuationModificationAndMandateRemainSeparate ≡ true
    sovereigntyIsReducedToExternalPhilosophicalInterpretation : Bool
    sovereigntyIsReducedToExternalPhilosophicalInterpretationIsFalse : sovereigntyIsReducedToExternalPhilosophicalInterpretation ≡ false

canonicalDrugGovernanceFarCrossPollinationBoundary : DrugGovernanceFarCrossPollinationBoundary
canonicalDrugGovernanceFarCrossPollinationBoundary =
  drugGovernanceFarCrossPollinationBoundary
    true refl false refl true refl true refl true refl false refl
