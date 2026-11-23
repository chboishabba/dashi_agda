module DASHI.Culture.AmyEskridgeTransparentPsiCorrectionAndModeratorWeldExact where

-- Original paper: Kekecs et al 2023, DOI 10.1098/rsos.191375
-- Original author correction: 2023 DOI 10.1098/rsos.231080
-- https://pmc.ncbi.nlm.nih.gov/articles/PMC10427810/
-- Original R code: Transparent_psi_RR_materials/
-- TPP_Statistical_analysis_script_FINAL.R, SHA
-- 4ec79f47bf11f73a6094dac1f3860a65f26e7a5d
--
-- THIS IS AN ADVERSARIAL PRIMARY-SOURCE AUDIT, not an accusation
-- of deliberate misconduct and not a replay of the full raw data.
-- The 2023 CORRECTION acknowledges:
-- (1) planned continuous *remote* GitLab code mirroring didn't happen;
--     local Git history and retrospective review replaced real-time audit;
-- (2) permanent server access logs were overwritten;
-- (3) independent auditor criterion relaxed due to practical recruitment;
-- (4) at least five restarted sessions might re-use participants;
-- (5) two test-account lab IDs were added ten days into data collection:
--     81 raw data records, of which 19 were erotic condition. They were
--     excluded in the final analysis; this requires true versioned code
--     and raw data reconciliation, not an automatic "perfectly preregistered".
--
-- The original 2023 methods explicitly state participants completed
-- sensation-seeking questionnaires to match Bem's protocol; these item
-- scores were *NOT used for primary hypothesis testing*. The final
-- R script computes the two-item SS score for descriptive summaries.
-- The SS_Q_item_1 item is reverse-coded; SS_Q_item_2 isn't.
-- Original Bem 2011 two items (p.410):
-- "I am easily bored"; "I often enjoy seeing movies I've seen before"
-- (the movie item reverse-scored), 1..5 averaged.
-- The current paper's "match Bem" claim and coding are compelling
-- prospective construct leads, but item order/languages and equivalence
-- need the original administered instrument and a mapping receipt.
--
-- Original 2015 proponent meta table (F1000Research 4:1188 v2):
-- 69 independent studies z=4.16, p=1.1e-5, BF=3853.
-- Bem's 25 Jan 2018 EMAIL instead says BF=3.85, a genuine
-- SOURCE-TO-SOURCE numerical conflict. Do not silently "correct"
-- a quotation or treat the two numbers as interchangeable.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)

import DASHI.Culture.AmyEskridgeTransparentPsiOriginalCodePriorSensitivityExact as TPP
import DASHI.Culture.AmyEskridgeBemExp1OriginalWorkbookReplayExact as Bem

record TPPPrimaryAuditCorrection : Set where
  constructor tpp-audit
  field
    originalProtocolRemoteGitLabContinuityMet : Bool
    originalServerLogsKeptPermanently : Bool
    originalAuditorIndependenceCriteriaMet : Bool
    atLeastRestartedSessions : Nat
    retrospectivelyAddedTestIdentifiers : Nat
    excludedTestRawRecords : Nat
    excludedTestEroticRecords : Nat
    firstStopEroticTrials : Nat
    fullReanalysisOfOriginalRawRowsHere : Bool
open TPPPrimaryAuditCorrection public

published2023AuthorCorrection : TPPPrimaryAuditCorrection
published2023AuthorCorrection =
  tpp-audit false false false 5 2 81 19 37836 false

publishedCorrectionTestRecords :
  excludedTestEroticRecords published2023AuthorCorrection ≡ 19
publishedCorrectionTestRecords = refl

publishedCorrectionSmallRelativeToAllEroticTrials :
  TPP.leq (excludedTestEroticRecords published2023AuthorCorrection * 1000)
    (firstStopEroticTrials published2023AuthorCorrection) ≡ true
publishedCorrectionSmallRelativeToAllEroticTrials = refl

data ModeratorStatus : Set where
  measuredButNotConfirmatory : ModeratorStatus
  preregisteredPrimaryModerator : ModeratorStatus

originalQuestionnaireStatus : ModeratorStatus
originalQuestionnaireStatus = measuredButNotConfirmatory

record CrossStudyMeasure : Set where
  constructor cross-study-measure
  field
    originalBemItems : Nat
    transparentPsiItems : Nat
    authorsIntendedProtocolMatch : Bool
    allAdministeredItemTextVerified : Bool
    confirmedEquivalentTranslations : Bool
    conditionBySeekInteractionIndependentlyReproduced : Bool

twoItemStimulusSeekingBridge : CrossStudyMeasure
twoItemStimulusSeekingBridge =
  cross-study-measure 2 2 true false false false

itemCountMatches :
  originalBemItems twoItemStimulusSeekingBridge ≡
  transparentPsiItems twoItemStimulusSeekingBridge
itemCountMatches = refl

noIndependentModeratorReplicationYet :
  conditionBySeekInteractionIndependentlyReproduced
    twoItemStimulusSeekingBridge ≡ false
noIndependentModeratorReplicationYet = refl

record MetaBayesFactorSourceConflict : Set where
  constructor meta-bf-conflict
  field
    published2015TableIntegerBF : Nat
    bem2018EmailBF100 : Nat
    matchingValueIndependentlyReconciled : Bool

bemMetaBFSourceConflict : MetaBayesFactorSourceConflict
bemMetaBFSourceConflict = meta-bf-conflict 3853 385 false

data MainNullLogitProvesModeratorWasAnalysed : Set where
data OpenRawDataProvesPerfectServerCodeAudit : Set where
data FiveRestartsEstablishPositivePsi : Set where
data PublishedMetaBayesFactorsAreIdentical : Set where

noOverallNullAsSubgroupTest :
  MainNullLogitProvesModeratorWasAnalysed → ⊥
noOverallNullAsSubgroupTest ()
noBornOpenAsPerfectCodeAudit :
  OpenRawDataProvesPerfectServerCodeAudit → ⊥
noBornOpenAsPerfectCodeAudit ()
noRestartAsPositiveEffect :
  FiveRestartsEstablishPositivePsi → ⊥
noRestartAsPositiveEffect ()
noUnreconciledBFEquivalence :
  PublishedMetaBayesFactorsAreIdentical → ⊥
noUnreconciledBFEquivalence ()

-- Retain original per-participant and correctly sourced prior gates.
directBemPriorIsNotLaterUsedPrior :
  Bem.originalHitCount + 2 ≡ TPP.originalTransparentPsiPriorSuccesses
directBemPriorIsNotLaterUsedPrior = refl
