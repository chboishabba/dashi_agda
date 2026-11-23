module DASHI.Economics.JPYTreasuryInterventionOfficialReceipts20261121Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- Original reported executions, distinct from Reuters-photo signalling.
-- Amounts are in TENTHS OF BILLIONS OF JPY (0.1 billion JPY).
-- US planned USD 5-10 billion is a different, incomparable unit.
------------------------------------------------------------------------

record OfficialFXReceipt : Set where
  constructor officialFXReceipt
  field
    operator : String
    operationDate : String
    yenBoughtTenthsBillion : Nat
    publisher : String
    originalURL : String
    knowledgeDate : String
    caveat : String
open OfficialFXReceipt public

japanJuly30 : OfficialFXReceipt
japanJuly30 = officialFXReceipt
  "Japan Ministry of Finance" "2026-07-30" 79756
  "Japan Ministry of Finance"
  "https://www.mof.go.jp/english/policy/international_policy/reference/feio/quarter/2026_3Qe.html"
  "2026-11-09"
  "Aggregate dated official intervention; publication on November 9 is not knowledge available to July 30 market participants."

japanJuly31 : OfficialFXReceipt
japanJuly31 = officialFXReceipt
  "Japan Ministry of Finance" "2026-07-31" 55523
  "Japan Ministry of Finance"
  "https://www.mof.go.jp/english/policy/international_policy/reference/feio/quarter/2026_3Qe.html"
  "2026-11-09"
  "Japanese executed amounts are distinct from US spot transactions."

japanAugust3 : OfficialFXReceipt
japanAugust3 = officialFXReceipt
  "Japan Ministry of Finance" "2026-08-03" 18714
  "Japan Ministry of Finance"
  "https://www.mof.go.jp/english/policy/international_policy/reference/feio/quarter/2026_3Qe.html"
  "2026-11-09"
  "Date is the operation date, not the reporting date."

usJuly31 : OfficialFXReceipt
usJuly31 = officialFXReceipt
  "New York Fed as fiscal agent of US Treasury" "2026-07-31" 794
  "Federal Reserve Bank of New York"
  "https://www.newyorkfed.org/medialibrary/media/newsevents/news/markets/2026/q3-2026-fx-quarterly-report.pdf"
  "2026-Q3-report-publication-date-to-acquire"
  "Executed purchase of 79.4 billion yen against sales of euros from ESF; not the Federal Reserve intervening on its own account."

japanQuarterTotal : Nat
japanQuarterTotal =
  yenBoughtTenthsBillion japanJuly30 +
  yenBoughtTenthsBillion japanJuly31 +
  yenBoughtTenthsBillion japanAugust3

japanTotalMatchesOfficial :
  japanQuarterTotal ≡ 153993
japanTotalMatchesOfficial = refl

usAndJapanAmountsDifferent :
  yenBoughtTenthsBillion usJuly31 ≡
  yenBoughtTenthsBillion japanJuly31 → ⊥
usAndJapanAmountsDifferent ()

data EvidenceClass : Set where
  proposedSignal officialExecutedOperation marketReportedInterpretation : EvidenceClass

record PhotoNote : Set where
  constructor photoNote
  field
    proposalLowerUSDmillion : Nat
    proposalUpperUSDmillion : Nat
    reportedOn : String
    source : String
    evidenceClass : EvidenceClass
open PhotoNote public

bessentNote : PhotoNote
bessentNote = photoNote
  5000 10000
  "2026-07-31"
  "https://www.reuters.com/world/asia-pacific/bessents-to-do-list-buy-5-10-billion-worth-japanese-yen-reuters-photo-shows-2026-07-31/"
  proposedSignal

-- No conversion of the proposal in USD into an executed JPY amount is supplied.
-- Even genuine intervention and exchange-rate response do not identify the
-- purported objective of inducing an equity crash or lowering Treasury yields.
data ProposalEqualsExecution : Set where
proposalNotExecution : ProposalEqualsExecution → ⊥
proposalNotExecution ()
