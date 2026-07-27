module DASHI.Governance.IsraelCyberLegalStatusCandidate where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_≤_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Governance.GeopoliticalDifferentialEvidence
open import DASHI.Governance.GeopoliticalGlobalPlayerCriterion

------------------------------------------------------------------------
-- Narrow source-bound fixture.
--
-- This module records only what the cited public sources support.  It does not
-- infer that aggregate high-tech/defence exports prove a trauma-to-cyber export
-- mechanism, and it does not collapse provisional/procedural ICJ orders into a
-- final merits judgment.

icjCase192Source : SourceReceipt
icjCase192Source =
  sourceReceipt
    "icj-case-192"
    "https://www.icj-cij.org/case/192"
    "International Court of Justice"
    "2025-04-14"
    "2026-07-26"
    "source-page-current-development-order-extension"
    "latest development records an extension of the counter-memorial time-limit"
    courtDocument

innovationAuthority2026Source : SourceReceipt
innovationAuthority2026Source =
  sourceReceipt
    "israel-innovation-report-2026"
    "https://innovationisrael.org.il/press_release/innovation-report-2026/"
    "Israel Innovation Authority"
    "2026-05-31"
    "2026-07-26"
    "official-2026-high-tech-report"
    "reports 2025 high-tech exports of 85 billion USD and fundraising near 15 billion USD"
    officialStatistic

defenceExports2024Source : SourceReceipt
defenceExports2024Source =
  sourceReceipt
    "israel-defence-exports-2024"
    "https://mod.gov.il/en/press-releases/press-room/israel-sets-new-record-in-defense-exports-over-147-billion-in-2024"
    "Israel Ministry of Defense"
    "2025-06-04"
    "2026-07-26"
    "official-defence-export-release-2024"
    "reports 14.795 billion USD in 2024 defence export agreements; intelligence information and cyber systems are listed as 4 percent of deal volume"
    officialStatistic

southAfricaIsraelProceduralStatus : LegalStatusReceipt
southAfricaIsraelProceduralStatus =
  legalStatusReceipt
    "International Court of Justice"
    "Application of the Genocide Convention in the Gaza Strip (South Africa v. Israel)"
    "192"
    counterMemorialPending
    "2025-04-14"
    "procedural extension of the counter-memorial time-limit; no final merits judgment is encoded"
    true
    icjCase192Source

noFinalMeritsFromCurrentFixture :
  FinalMeritsStatus counterMemorialPending → ⊥
noFinalMeritsFromCurrentFixture =
  counterMemorialPendingDoesNotEntailFinalMeritsJudgment

aggregateHighTechEvidence : CyberExportEvidence
aggregateHighTechEvidence =
  cyberExportEvidence
    (measuredAmount 85000000000 usd "aggregate Israeli high-tech exports in 2025")
    (measuredAmount 15000000000 usd "approximate aggregate Israeli high-tech fundraising in 2025")
    0
    0
    2025
    "official aggregate high-tech indicators; no cyber-only global-share or company-count denominator supplied"
    innovationAuthority2026Source
    "aggregate evidence only: it cannot by itself establish the cyber-specific global-player criterion"

defenceCyberShareEvidence : CyberExportEvidence
defenceCyberShareEvidence =
  cyberExportEvidence
    (measuredAmount 14795000000 usd "total Israeli defence export agreements in 2024")
    (measuredAmount 0 unspecifiedCurrency "not an investment measure")
    400
    0
    2024
    "official defence-export category share; 400 basis points records the listed 4 percent intelligence information and cyber systems category"
    defenceExports2024Source
    "defence category evidence is not equivalent to the civilian cybersecurity market and does not identify particular deployments"

------------------------------------------------------------------------
-- An explicit cyber-specific threshold cannot be discharged by aggregate
-- high-tech evidence whose cyber share and cyber company denominator are both
-- recorded as unavailable (zero in this fail-closed fixture).

minimalCyberSpecificCriterion : ConcreteGlobalPlayerCriterion
minimalCyberSpecificCriterion =
  concreteGlobalPlayerCriterion
    usd
    1
    1
    1
    2025
    "minimal executable criterion requiring positive cyber-specific exports, share, and company count"

oneNotLeZero : suc zero ≤ zero → ⊥
oneNotLeZero ()

aggregateHighTechCannotMeetCyberSpecificCriterion :
  ConcreteGlobalPlayerSupported
    minimalCyberSpecificCriterion
    aggregateHighTechEvidence →
  ⊥
aggregateHighTechCannotMeetCyberSpecificCriterion support =
  oneNotLeZero (globalShareThresholdMet support)

candidateScope : GeopoliticalClaimScope
candidateScope =
  geopoliticalClaimScope
    "israel-cyber-export-trauma-mechanism-candidate"
    "Israel and international export markets"
    "2024"
    "2026"
    "institutional and affected-population scope unresolved"
    "cybersecurity high-tech and defence export sectors"
    "cybersecurity surveillance intelligence and information systems"

data MissingFixtureAxis : Set where
  cyberOnlyExportValue : MissingFixtureAxis
  cyberCompanyDenominator : MissingFixtureAxis
  productBuyerDeployment : MissingFixtureAxis
  occupationToDoctrineMechanism : MissingFixtureAxis
  doctrineToExportCausation : MissingFixtureAxis
  counterevidenceFibrePopulation : MissingFixtureAxis

missingFixtureAxes : List MissingFixtureAxis
missingFixtureAxes =
  cyberOnlyExportValue
  ∷ cyberCompanyDenominator
  ∷ productBuyerDeployment
  ∷ occupationToDoctrineMechanism
  ∷ doctrineToExportCausation
  ∷ counterevidenceFibrePopulation
  ∷ []

record CandidateFixtureAssessment : Set where
  constructor candidateFixtureAssessment
  field
    economicPresenceStatus : Trit
    legalFinalMeritsStatus : Trit
    traumaExportMechanismStatus : Trit
    interpretation : String

candidateAssessment : CandidateFixtureAssessment
candidateAssessment =
  candidateFixtureAssessment
    pos
    neg
    zer
    "economic/export significance is source-supported at aggregate level; a final ICJ merits judgment is not present; the trauma-to-export mechanism remains undetermined pending cyber-specific denominator, product-level deployment, and causal evidence"

-- Constructorless promotion token: the current fixture cannot promote the
-- candidate mechanism while its required axes remain uninhabited.
data IsraelCyberTraumaExportPromotion : Set where

currentFixtureCannotPromoteMechanism :
  IsraelCyberTraumaExportPromotion → ⊥
currentFixtureCannotPromoteMechanism ()
