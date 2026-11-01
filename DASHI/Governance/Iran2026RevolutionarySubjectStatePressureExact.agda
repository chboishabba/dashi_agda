module DASHI.Governance.Iran2026RevolutionarySubjectStatePressureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- CURRENT 2026 IRAN STATE / PRESSURE / REPRESSION SOURCE ATLAS
------------------------------------------------------------------------

reutersMojtaba : Source.AttributedSource
reutersMojtaba = Source.mkNoDOISource
  "Reuters"
  "Iran names Khamenei's hardline son Mojtaba as new supreme leader, oil surges"
  "Reuters"
  "2026-03-08"
  "https://www.reuters.com/world/europe/trump-rejects-settling-iran-war-raises-prospect-killing-all-its-potential-2026-03-08/"
  Source.newsSource
  "current secondary report on Mojtaba Khamenei's selection as Supreme Leader by the Assembly of Experts"
  Source.publicAttribution

reutersTaebPressure : Source.AttributedSource
reutersTaebPressure = Source.mkNoDOISource
  "Reuters"
  "Battered by war, Iran's rulers wary of more economic pain and unrest if US tightens pressure"
  "Reuters"
  "2026-08-17"
  "https://www.reuters.com/world/middle-east/battered-by-war-irans-rulers-wary-more-economic-pain-unrest-if-us-tightens-2026-08-17/"
  Source.newsSource
  "current report on wartime economic strain, inflation, unrest concerns, Hossein Taeb's appointment to lead the Basij, and use of Basij/IRGC in protest suppression"
  Source.publicAttribution

reutersHouseholdPressure : Source.AttributedSource
reutersHouseholdPressure = Source.mkNoDOISource
  "Reuters"
  "Iranians stagger under soaring costs of seven months of war"
  "Reuters"
  "2026-09-29"
  "https://www.reuters.com/business/energy/iranians-stagger-under-soaring-costs-seven-months-war-2026-09-29/"
  Source.newsSource
  "current reporting on blockade-related revenue loss, household hardship, employment pressure, fear, repression and negotiation incentives"
  Source.publicAttribution

record CurrentStateReceipt : Set where
  constructor current-state-receipt
  field
    receiptRef : String
    source : Source.AttributedSource
    boundedReading : String
    currentFactPaid : Bool
    currentFactPaidIsTrue : currentFactPaid ≡ true
    historicalMeaningRewritten : Bool
    historicalMeaningRewrittenIsFalse :
      historicalMeaningRewritten ≡ false
    causalNecessityPaid : Bool
    causalNecessityPaidIsFalse :
      causalNecessityPaid ≡ false

open CurrentStateReceipt public

currentSupremeLeaderReceipt : CurrentStateReceipt
currentSupremeLeaderReceipt =
  current-state-receipt
    "iran-2026:supreme-leader"
    reutersMojtaba
    "Reuters reports Mojtaba Khamenei was selected as Supreme Leader in March 2026."
    true refl
    false refl
    false refl

currentBasijCommandReceipt : CurrentStateReceipt
currentBasijCommandReceipt =
  current-state-receipt
    "iran-2026:basij-command"
    reutersTaebPressure
    "Reuters reports Hossein Taeb's appointment to lead the Basij amid leadership concern over renewed unrest."
    true refl
    false refl
    false refl

currentEconomicPressureReceipt : CurrentStateReceipt
currentEconomicPressureReceipt =
  current-state-receipt
    "iran-2026:economic-pressure"
    reutersHouseholdPressure
    "Reuters documents severe household and revenue pressure during the war and blockade."
    true refl
    false refl
    false refl

data CurrentLeadershipExplainsHistoricalMeaning : Set where
data EconomicPressureNecessitatesRepression : Set where
data BasijCommandProvesEveryBasijAction : Set where

currentLeadershipDoesNotRewriteHistoricalMeaning :
  CurrentLeadershipExplainsHistoricalMeaning → ⊥
currentLeadershipDoesNotRewriteHistoricalMeaning ()

economicPressureDoesNotNecessitateRepression :
  EconomicPressureNecessitatesRepression → ⊥
economicPressureDoesNotNecessitateRepression ()

commandReceiptDoesNotProveEveryAction :
  BasijCommandProvesEveryBasijAction → ⊥
commandReceiptDoesNotProveEveryAction ()

currentAtlas : Source.AttributedSourceAtlas
currentAtlas = Source.mkSourceAtlas
  "Iran 2026 revolutionary-subject/state-pressure atlas"
  "DASHI.Governance.Iran2026RevolutionarySubjectStatePressureExact"
  (reutersMojtaba ∷ reutersTaebPressure ∷ reutersHouseholdPressure ∷ [])
  "current leadership, security command and economic-pressure facts only; no historical-semantic or causal-necessity promotion"

mojtabaSnowball : Snowball.SourceRoleSnowballReceipt reutersMojtaba
mojtabaSnowball = Snowball.canonicalSourceRoleSnowballReceipt reutersMojtaba
