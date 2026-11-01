module DASHI.Governance.ExternalThreatRepressionMechanismTransferExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Governance.SiegePressureDomesticDivergenceHypothesisExact as Siege

------------------------------------------------------------------------
-- EXTERNAL THREAT -> REPRESSION MECHANISM TRANSFER
--
-- General comparative evidence supplies a causal prior:
--   external threat can directly increase repression by giving political cover,
--   while indirectly reducing repression through increased state capacity.
--
-- Iran-specific evidence supplies a live case surface, but the transfer into a
-- closed Iran-specific mechanism remains an explicit residual.
------------------------------------------------------------------------

artabeEtAl2023 : Source.AttributedSource
artabeEtAl2023 = Source.mkDOISource
  "Eugenia Artabe, Samantha Chapa, Leah Sparkman, Patrick E. Shea"
  "External Threats, Capacity, and Repression: How the Threat of War Affects Political Development and Physical Integrity Rights"
  "British Journal of Political Science 53(4):1311-1327"
  "2023"
  "10.1017/S0007123422000692"
  "https://www.cambridge.org/core/journals/british-journal-of-political-science/article/external-threats-capacity-and-repression-how-the-threat-of-war-affects-political-development-and-physical-integrity-rights/86BD49D962109C9F584FB97EE52FD283"
  Source.academicArticleSource
  "cross-national causal study: external threats directly increase repression but indirectly can decrease repression via increased state capacity; used as general mechanism evidence, not Iran-specific proof"
  Source.publicAttribution

heffington2021 : Source.AttributedSource
heffington2021 = Source.mkDOISource
  "Colton Heffington"
  "External threat and human rights: How international conflict leads to domestic repression"
  "Journal of Human Rights 20(1):2-19"
  "2021"
  "10.1080/14754835.2020.1803052"
  "https://www.tandfonline.com/doi/abs/10.1080/14754835.2020.1803052"
  Source.academicArticleSource
  "cross-national evidence that threatening international conflict can worsen physical-integrity and some civil rights; general mechanism evidence only"
  Source.publicAttribution

iranStrikesNBER2026 : Source.AttributedSource
iranStrikesNBER2026 = Source.mkDOISource
  "Sultan Mehmood, Yaroslav Prokhorskoy, Leonard Wantchekon"
  "Strategic Sovereignty: U.S.-Israeli Strikes and the Reversal of Anti-Regime Protest in Iran"
  "NBER Working Paper 35734"
  "2026"
  "10.3386/w35734"
  "https://www.nber.org/papers/w35734"
  (Source.namedSourceKind "economics/political-economy working paper")
  "Iran-specific study of 2026 strike exposure and protest composition; reports anti-government protest receding amid repression/foreign-agent narrative before strikes and a shift toward pro-government/anti-US-Israel mobilisation after strike exposure"
  Source.publicAttribution

record GeneralThreatRepressionMechanism : Set where
  constructor general-threat-repression-mechanism
  field
    source : Source.AttributedSource
    directPath : String
    indirectPath : String
    generalCausalEvidencePaid : Bool
    generalCausalEvidencePaidIsTrue :
      generalCausalEvidencePaid ≡ true
    monotoneMoreThreatMoreRepression : Bool
    monotoneMoreThreatMoreRepressionIsFalse :
      monotoneMoreThreatMoreRepression ≡ false
    universalAcrossCases : Bool
    universalAcrossCasesIsFalse :
      universalAcrossCases ≡ false

open GeneralThreatRepressionMechanism public

generalMechanism : GeneralThreatRepressionMechanism
generalMechanism =
  general-threat-repression-mechanism
    artabeEtAl2023
    "external threat can provide leaders political cover to repress opponents"
    "external threat can also induce state-capacity investment that reduces repression"
    true refl
    false refl
    false refl

record CaseTransferReceipt : Set where
  constructor case-transfer-receipt
  field
    caseRef : String
    generalMechanism : GeneralThreatRepressionMechanism
    caseSource : Source.AttributedSource
    caseHasExternalThreatSurface : Bool
    caseHasExternalThreatSurfaceIsTrue :
      caseHasExternalThreatSurface ≡ true
    caseHasRepressionSurface : Bool
    caseHasRepressionSurfaceIsTrue :
      caseHasRepressionSurface ≡ true
    caseHasMobilisationShiftEvidence : Bool
    caseHasMobilisationShiftEvidenceIsTrue :
      caseHasMobilisationShiftEvidence ≡ true
    caseSpecificCausalMechanismClosed : Bool
    caseSpecificCausalMechanismClosedIsFalse :
      caseSpecificCausalMechanismClosed ≡ false

open CaseTransferReceipt public

iran2026Transfer : CaseTransferReceipt
iran2026Transfer =
  case-transfer-receipt
    "Iran-2026"
    generalMechanism
    iranStrikesNBER2026
    true refl
    true refl
    true refl
    false refl

record TransferResidual : Set where
  constructor transfer-residual
  field
    residualRef : String
    requiredEvidence : String
    counterHypotheses : String
    generalMechanismPaid : Bool
    generalMechanismPaidIsTrue :
      generalMechanismPaid ≡ true
    caseSpecificClosurePaid : Bool
    caseSpecificClosurePaidIsFalse :
      caseSpecificClosurePaid ≡ false

open TransferResidual public

iranCaseSpecificResidual : TransferResidual
iranCaseSpecificResidual =
  transfer-residual
    "residual:iran-2026:external-threat-domestic-repression"
    "Iran-specific identification of whether external threat caused a particular repression increment, rather than merely co-occurring with repression and shifting mobilisation"
    "pre-existing repression; domestic regime-security interests; protest intensity; economic crisis; state-capacity changes; foreign-agent framing as independent mediator"
    true refl
    false refl

data GeneralMechanismAutomaticallyTransfersToIran : Set where
data ExternalThreatOnlyIncreasesRepression : Set where
data StrikeMobilisationShiftProvesRepressionNecessity : Set where
data WorkingPaperCreatesFinalAuthority : Set where

generalMechanismDoesNotAutoTransfer :
  GeneralMechanismAutomaticallyTransfersToIran → ⊥
generalMechanismDoesNotAutoTransfer ()

threatEffectIsNotMonotoneByDefinition :
  ExternalThreatOnlyIncreasesRepression → ⊥
threatEffectIsNotMonotoneByDefinition ()

mobilisationShiftDoesNotProveRepressionNecessity :
  StrikeMobilisationShiftProvesRepressionNecessity → ⊥
mobilisationShiftDoesNotProveRepressionNecessity ()

workingPaperDoesNotCreateFinalAuthority :
  WorkingPaperCreatesFinalAuthority → ⊥
workingPaperDoesNotCreateFinalAuthority ()

artabeSnowball :
  Snowball.SourceRoleSnowballReceipt artabeEtAl2023
artabeSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt artabeEtAl2023

nberSnowball :
  Snowball.SourceRoleSnowballReceipt iranStrikesNBER2026
nberSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt iranStrikesNBER2026

existingIranHypothesis : Siege.MechanismHypothesis
existingIranHypothesis = Siege.iranSiegeHypothesis
