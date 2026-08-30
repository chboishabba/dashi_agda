module DASHI.Governance.ReligiousChildhoodFeministWitchRegression where

------------------------------------------------------------------------
-- Focused regression for the religious-childhood / feminist-self-formation /
-- witch-history cross-pollination tranche.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Governance.ReligiousChildhoodSubjectFormationBidiExact as Formation
import DASHI.Governance.ReligiousChildhoodInstantiationEvidenceAtlasExact as Atlas
import DASHI.Governance.WitchTrialEvidenceSubjectAttributionExact as WitchTrial
import DASHI.Governance.SuffrageWitchReclamationGenealogyExact as Genealogy
import DASHI.Governance.HistoricalEventMeaningProvenanceBidiExact as History

------------------------------------------------------------------------
-- Fine-state route survives public behavioural collapse.
------------------------------------------------------------------------

formationRouteRegression :
  INF.FactorsThrough Formation.publicReligiousBehaviour Formation.formationRoute → ⊥
formationRouteRegression = Formation.publicBehaviourCannotRecoverFormationRoute

------------------------------------------------------------------------
-- Spectral-report surface does not determine causal mechanism.
------------------------------------------------------------------------

spectralMechanismRegression :
  INF.FactorsThrough WitchTrial.spectralReport WitchTrial.causalMechanism → ⊥
spectralMechanismRegression = WitchTrial.spectralReportCannotRecoverMechanism

------------------------------------------------------------------------
-- Accusation and self-identification remain different identity sources.
------------------------------------------------------------------------

accusationIdentityRegression :
  WitchTrial.externallyAccusedWitch ≡ WitchTrial.selfIdentifiedWitch → ⊥
accusationIdentityRegression = WitchTrial.accusation≠selfIdentification

------------------------------------------------------------------------
-- Historical reinterpretation does not manufacture practitioner continuity.
------------------------------------------------------------------------

noPractitionerLineagePromotionRegression :
  Genealogy.ReinterpretationPromotesPractitionerLineage → ⊥
noPractitionerLineagePromotionRegression =
  Genealogy.reinterpretationDoesNotPromotePractitionerLineage

noSalemWiccaPromotionRegression :
  Genealogy.ModernWiccaPromotesSalemWiccanIdentity → ⊥
noSalemWiccaPromotionRegression =
  Genealogy.modernWiccaDoesNotPromoteSalemWiccanIdentity

------------------------------------------------------------------------
-- Shared historical-event discipline: a burned-factory surface cannot recover
-- accidental versus politically motivated cause.
------------------------------------------------------------------------

factoryCauseRegression :
  INF.FactorsThrough History.factorySurface History.fireCause → ⊥
factoryCauseRegression = History.burnedSurfaceCannotRecoverCause

------------------------------------------------------------------------
-- Empirical atlas remains partial rather than decorative completion.
------------------------------------------------------------------------

religiousChildhoodInstantiationRegression :
  Atlas.ReligiousChildhoodInstantiationReceipt
religiousChildhoodInstantiationRegression =
  Atlas.canonicalReligiousChildhoodInstantiationReceipt

------------------------------------------------------------------------
-- Regression boundary.
------------------------------------------------------------------------

record ReligiousChildhoodFeministWitchRegressionBoundary : Set where
  constructor religious-childhood-feminist-witch-regression-boundary
  field
    publicConformityRecoversFormation : Bool
    spectralReportRecoversMechanism : Bool
    accusedWitchEqualsSelfIdentifiedWitch : Bool
    suffrageReinterpretationProvesUnbrokenWiccanLineage : Bool
    burnedFactoryRecoversPoliticalCause : Bool
    currentReligiousAtlasIsCausallyComplete : Bool
    currentReligiousAtlasIsPartiallyInstantiated : Bool

canonicalReligiousChildhoodFeministWitchRegressionBoundary :
  ReligiousChildhoodFeministWitchRegressionBoundary
canonicalReligiousChildhoodFeministWitchRegressionBoundary =
  religious-childhood-feminist-witch-regression-boundary
    false false false false false false true
