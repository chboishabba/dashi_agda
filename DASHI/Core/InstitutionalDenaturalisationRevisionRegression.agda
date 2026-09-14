module DASHI.Core.InstitutionalDenaturalisationRevisionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.InstitutionalDenaturalisationRevisionExact as Revision

parentNormProductionReusedRegression :
  Revision.parentNormProductionReused Revision.canonicalInstitutionalDenaturalisationBoundary
  ≡ true
parentNormProductionReusedRegression = refl

appendOnlyParentReusedRegression :
  Revision.appendOnlyRevisionParentReused Revision.canonicalInstitutionalDenaturalisationBoundary
  ≡ true
appendOnlyParentReusedRegression = refl

baselinePersistsRegression :
  Revision.BaselineContains Revision.baselineObservation
    (Revision.appendInstitutionalEvidence
      Revision.baselineOnlyHistory
      Revision.productionHistoryEvidence)
baselinePersistsRegression = Revision.baselineInExtended

interpretationRevisionRegression :
  Revision.InstitutionalInterpretationRevision
interpretationRevisionRegression = Revision.canonicalInstitutionalInterpretationRevision

laterEvidenceRewritesEarlierObservationRegression :
  Revision.laterEvidenceAutomaticallyRewritesEarlierObservation
    Revision.canonicalInstitutionalDenaturalisationBoundary
  ≡ false
laterEvidenceRewritesEarlierObservationRegression = refl

denaturalisationInvalidatesAllPriorActionsRegression :
  Revision.denaturalisationAutomaticallyInvalidatesEveryPriorInstitutionalAction
    Revision.canonicalInstitutionalDenaturalisationBoundary
  ≡ false
denaturalisationInvalidatesAllPriorActionsRegression = refl

historyCanChangeInterpretationRegression :
  Revision.productionHistoryEvidenceMayChangeCurrentInterpretation
    Revision.canonicalInstitutionalDenaturalisationBoundary
  ≡ true
historyCanChangeInterpretationRegression = refl
