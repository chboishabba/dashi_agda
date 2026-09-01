module DASHI.Governance.HistoricalDrugGovernanceClassifierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as HT
import DASHI.Governance.DrugClassificationAsymmetryDiscriminatorExact as Classify
import DASHI.Governance.WarOnDrugsHistoricalGenealogyExact as Genealogy

------------------------------------------------------------------------
-- HISTORY-INDEXED DRUG-GOVERNANCE CLASSIFIER
--
-- The governance route is not a timeless function of substance/carrier alone.
-- Institutional classifier versions can change across historical epochs.  The
-- fixture is synthetic and proves the geometry of classifier revision; it does
-- not assert that every historical person with the same profile encountered the
-- exact route encoded here.
------------------------------------------------------------------------

data DrugPolicyEpoch : Set where
  anslingerFederalProhibitionEpoch
  nixonBifurcatedWarOnDrugsEpoch
  reaganPunitiveEscalationEpoch
  trumpPsychedelicSplitEpoch
  : DrugPolicyEpoch

data ClassifierVersion : Set where
  federalNarcoticsVersion
  nixonEnforcementTreatmentVersion
  reaganEscalationVersion
  trumpPunitiveTherapeuticSplitVersion
  : ClassifierVersion

data DrugPolicyHistory : Set where
  canonicalUnitedStatesDrugPolicyHistory : DrugPolicyHistory

data HistoricalCarrierProfile : Set where
  veteranDiagnosedPsilocybinProfile
  counterculturePsilocybinProfile
  genericStreetPsilocybinProfile
  indigenousCeremonialPsilocybinProfile
  : HistoricalCarrierProfile

------------------------------------------------------------------------
-- Same carrier profile, different historical classifier.
------------------------------------------------------------------------

classifierAt : DrugPolicyEpoch → HistoricalCarrierProfile → Classify.GovernanceCone
classifierAt anslingerFederalProhibitionEpoch veteranDiagnosedPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt nixonBifurcatedWarOnDrugsEpoch veteranDiagnosedPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt reaganPunitiveEscalationEpoch veteranDiagnosedPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt trumpPsychedelicSplitEpoch veteranDiagnosedPsilocybinProfile =
  Classify.careResearchCone

classifierAt anslingerFederalProhibitionEpoch counterculturePsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt nixonBifurcatedWarOnDrugsEpoch counterculturePsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt reaganPunitiveEscalationEpoch counterculturePsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt trumpPsychedelicSplitEpoch counterculturePsilocybinProfile =
  Classify.mixedOrUnresolvedCone

classifierAt anslingerFederalProhibitionEpoch genericStreetPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt nixonBifurcatedWarOnDrugsEpoch genericStreetPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt reaganPunitiveEscalationEpoch genericStreetPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt trumpPsychedelicSplitEpoch genericStreetPsilocybinProfile =
  Classify.punitiveSecurityCone

classifierAt anslingerFederalProhibitionEpoch indigenousCeremonialPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt nixonBifurcatedWarOnDrugsEpoch indigenousCeremonialPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt reaganPunitiveEscalationEpoch indigenousCeremonialPsilocybinProfile =
  Classify.punitiveSecurityCone
classifierAt trumpPsychedelicSplitEpoch indigenousCeremonialPsilocybinProfile =
  Classify.sovereignCeremonialCone

versionAt : DrugPolicyEpoch → ClassifierVersion
versionAt anslingerFederalProhibitionEpoch = federalNarcoticsVersion
versionAt nixonBifurcatedWarOnDrugsEpoch = nixonEnforcementTreatmentVersion
versionAt reaganPunitiveEscalationEpoch = reaganEscalationVersion
versionAt trumpPsychedelicSplitEpoch = trumpPunitiveTherapeuticSplitVersion

------------------------------------------------------------------------
-- Exact historical reclassification witness.
------------------------------------------------------------------------

veteranProfileReclassifiedBy2026 :
  classifierAt nixonBifurcatedWarOnDrugsEpoch veteranDiagnosedPsilocybinProfile
  ≡
  classifierAt trumpPsychedelicSplitEpoch veteranDiagnosedPsilocybinProfile
  → ⊥
veteranProfileReclassifiedBy2026 ()

genericStreetProfileRemainsPunitiveAcrossSelectedEpochs :
  classifierAt nixonBifurcatedWarOnDrugsEpoch genericStreetPsilocybinProfile
  ≡
  classifierAt trumpPsychedelicSplitEpoch genericStreetPsilocybinProfile
genericStreetProfileRemainsPunitiveAcrossSelectedEpochs = refl

------------------------------------------------------------------------
-- Generic history/time consumer-fibre instantiation.
------------------------------------------------------------------------

data AlwaysLive (profile : HistoricalCarrierProfile) : Set where
  live : AlwaysLive profile

historyTimeSurface : HT.HistoryTimeConsumerFibreSurface
historyTimeSurface = HT.historyTimeConsumerFibreSurface
  DrugPolicyHistory
  DrugPolicyEpoch
  HistoricalCarrierProfile
  Classify.GovernanceCone
  ClassifierVersion
  (λ _ _ profile → AlwaysLive profile)
  (λ _ epoch profile → classifierAt epoch profile)
  (λ _ epoch → versionAt epoch)
  "historical drug-policy carrier fibre"
  "history-indexed care/punishment/ceremonial governance classifier"
  "Anslinger/Nixon/Reagan/Trump-era classifier version"

------------------------------------------------------------------------
-- Consumer revision needs its own historical authority.  We do not transport
-- the 1971 classification closure through the 2026 rule change for free.
------------------------------------------------------------------------

record ClassifierRevisionReceipt
    (before after : DrugPolicyEpoch) : Set where
  constructor classifierRevisionReceipt
  field
    beforeVersion : ClassifierVersion
    afterVersion : ClassifierVersion
    beforeVersionIs : beforeVersion ≡ versionAt before
    afterVersionIs : afterVersion ≡ versionAt after
    legalPolicyReference : String
    scientificMedicalReference : String
    enforcementReference : String
    affectedCarrierReference : String
    revisionIsNotRetroactiveHistoricalErasure : Bool
    revisionIsNotRetroactiveHistoricalErasureIsTrue :
      revisionIsNotRetroactiveHistoricalErasure ≡ true

open ClassifierRevisionReceipt public

nixonToTrumpRevision :
  ClassifierRevisionReceipt
    nixonBifurcatedWarOnDrugsEpoch
    trumpPsychedelicSplitEpoch
nixonToTrumpRevision = classifierRevisionReceipt
  nixonEnforcementTreatmentVersion
  trumpPunitiveTherapeuticSplitVersion
  refl refl
  "1970 Controlled Substances Act / 1971 Nixon drug-war launch / later 2026 psychedelic access policy"
  "research reopening and 2026 veteran psychedelic clinical route"
  "punitive illicit-supply enforcement remains independently active"
  "veteran/diagnosed/clinical and ceremonial carriers acquire routes unavailable under earlier synthetic classifier"
  true refl

------------------------------------------------------------------------
-- Same current carrier surface does not determine governance without the
-- historical classifier/version coordinate.
------------------------------------------------------------------------

data CoarseCarrierSurface : Set where
  sameVeteranPsilocybinCarrierSurface : CoarseCarrierSurface

coarseCarrierObserver :
  DrugPolicyEpoch → HistoricalCarrierProfile → CoarseCarrierSurface
coarseCarrierObserver _ veteranDiagnosedPsilocybinProfile =
  sameVeteranPsilocybinCarrierSurface
coarseCarrierObserver _ counterculturePsilocybinProfile =
  sameVeteranPsilocybinCarrierSurface
coarseCarrierObserver _ genericStreetPsilocybinProfile =
  sameVeteranPsilocybinCarrierSurface
coarseCarrierObserver _ indigenousCeremonialPsilocybinProfile =
  sameVeteranPsilocybinCarrierSurface

sameCoarseCarrierDifferentClassifierOutcome :
  coarseCarrierObserver nixonBifurcatedWarOnDrugsEpoch veteranDiagnosedPsilocybinProfile
  ≡
  coarseCarrierObserver trumpPsychedelicSplitEpoch veteranDiagnosedPsilocybinProfile
sameCoarseCarrierDifferentClassifierOutcome = refl

historicalClassifierChangesReachableCone :
  classifierAt nixonBifurcatedWarOnDrugsEpoch veteranDiagnosedPsilocybinProfile
  ≡
  classifierAt trumpPsychedelicSplitEpoch veteranDiagnosedPsilocybinProfile
  → ⊥
historicalClassifierChangesReachableCone ()

historicalGenealogyBoundary : Genealogy.WarOnDrugsHistoricalGenealogyBoundary
historicalGenealogyBoundary = Genealogy.canonicalWarOnDrugsHistoricalGenealogyBoundary

record HistoricalDrugGovernanceClassifierBoundary : Set where
  constructor historicalDrugGovernanceClassifierBoundary
  field
    governanceClassifierIsTimeIndexed : Bool
    governanceClassifierIsTimeIndexedIsTrue :
      governanceClassifierIsTimeIndexed ≡ true
    sameCarrierSurfaceCanReceiveDifferentHistoricalRoute : Bool
    sameCarrierSurfaceCanReceiveDifferentHistoricalRouteIsTrue :
      sameCarrierSurfaceCanReceiveDifferentHistoricalRoute ≡ true
    classifierRevisionNeedsSeparateAuthority : Bool
    classifierRevisionNeedsSeparateAuthorityIsTrue :
      classifierRevisionNeedsSeparateAuthority ≡ true
    therapeuticReclassificationErasesPriorPunitiveHistory : Bool
    therapeuticReclassificationErasesPriorPunitiveHistoryIsFalse :
      therapeuticReclassificationErasesPriorPunitiveHistory ≡ false
    allCarriersMoveTogetherWhenClassifierChanges : Bool
    allCarriersMoveTogetherWhenClassifierChangesIsFalse :
      allCarriersMoveTogetherWhenClassifierChanges ≡ false

canonicalHistoricalDrugGovernanceClassifierBoundary :
  HistoricalDrugGovernanceClassifierBoundary
canonicalHistoricalDrugGovernanceClassifierBoundary =
  historicalDrugGovernanceClassifierBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
