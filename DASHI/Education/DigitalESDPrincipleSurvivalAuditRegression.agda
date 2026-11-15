module DASHI.Education.DigitalESDPrincipleSurvivalAuditRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (false)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDPrincipleSurvivalAuditExact as S
import DASHI.Education.DigitalESDTransferablePedagogicalPrinciplesExact as D

allCandidateStatus : S.PrincipleSurvivalReceipt.actualCorpusAdjudicationObserved S.engagement ≡ false
allCandidateStatus = refl

agencyNeedsSeparateCollectiveAction :
  S.PrincipleSurvivalReceipt.candidateVerdict S.agency ≡ S.provisionalSplitCandidate
agencyNeedsSeparateCollectiveAction = refl

custodianshipIsProvisional :
  S.PrincipleSurvivalReceipt.currentReviewStage S.custodianship ≡ S.attributedPreSearchSynthesis
custodianshipIsProvisional = refl

noSevenValidated : S.SevenPrinciplesEmpiricallyValidated → ⊥
noSevenValidated = S.noPrematureValidation
