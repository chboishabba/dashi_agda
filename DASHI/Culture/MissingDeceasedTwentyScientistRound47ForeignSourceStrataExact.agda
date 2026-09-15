module DASHI.Culture.MissingDeceasedTwentyScientistRound47ForeignSourceStrataExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 47: FOREIGN-SOURCE EVIDENCE STRATA
--
-- Non-US material is useful because it can independently pay identity,
-- institutional role, technical domain, date/cause wording, and local event
-- details.  It must not be promoted into programme linkage or causation merely
-- because it originates in another jurisdiction or agrees with US reporting.
------------------------------------------------------------------------

data ForeignSourceRole : Set where
  chinaDomesticPrimaryLike
  hongKongIndependentReporting
  nonUSCrossNationalComparison : ForeignSourceRole

record ForeignSourceReceipt : Set where
  constructor foreign-source-receipt
  field
    personOrCluster : String
    sourceRole : ForeignSourceRole
    sourceDescription : String
    pays : String
    doesNotPay : String
    sameObjectOrEventCorroborationPaid : Bool
    H2Paid : Bool
    H3Paid : Bool

open ForeignSourceReceipt public

fangCAS : ForeignSourceReceipt
fangCAS = foreign-source-receipt
  "Fang Daining"
  chinaDomesticPrimaryLike
  "Chinese Academy of Sciences obituary, 2026"
  "identity, death on 27 February 2026 from illness, advanced materials/structural mechanics role, and contribution to national-defence equipment development"
  "hypersonic-programme causation, foul play, shared cohort programme, targeting, or concealment"
  true false false

fangDomesticPress : ForeignSourceReceipt
fangDomesticPress = foreign-source-receipt
  "Fang Daining"
  chinaDomesticPrimaryLike
  "The Paper / Red Star News domestic reporting following CAS publication"
  "independent domestic republication of CAS death notice and reporting that a former student understood Fang died while abroad for an academic conference"
  "a verified medical mechanism beyond the CAS illness wording, or any hostile mechanism"
  true false false

yanSCMP : ForeignSourceReceipt
yanSCMP = foreign-source-receipt
  "Yan Hong"
  hongKongIndependentReporting
  "South China Morning Post, 27 March 2026"
  "NPU identity, death after illness, hypersonic/high-speed propulsion and plasma-flow-control work, and national project participation"
  "one shared cohort programme, targeting, or causal relation to research"
  true false false

fangSCMP : ForeignSourceReceipt
fangSCMP = foreign-source-receipt
  "Fang Daining"
  hongKongIndependentReporting
  "South China Morning Post, March-May 2026"
  "independent reporting of Fang's death, defence-relevant advanced-materials/hypersonic context, and later CAS confirmation"
  "verification of online claims about an unexpected medical episode, suppression of obituary photographs, or foul play"
  true false false

chinaNineComparison : ForeignSourceReceipt
chinaNineComparison = foreign-source-receipt
  "reported Chinese nine-person scientist cluster"
  nonUSCrossNationalComparison
  "India Today, 24 April 2026, comparing nine Chinese cases with the US missing/deceased-scientist pattern"
  "existence of a non-US externally assembled comparative cohort and public cross-national salience"
  "formal Chinese-government investigation, formal US congressional inclusion of the nine deaths, one causal mechanism, or targeting"
  true false false

wangDanhauChinaEmbassy : ForeignSourceReceipt
wangDanhauChinaEmbassy = foreign-source-receipt
  "Wang Danhao (outside retained 20; comparator only)"
  hongKongIndependentReporting
  "SCMP reporting of Chinese embassy confirmation and request for investigation after Wang's 2026 death in the United States"
  "an example that Chinese official actors have publicly treated at least one scientist death abroad as a matter requiring explanation"
  "membership in the retained 20, membership in the reported Chinese nine, or a link to the cohort's deaths"
  true false false

round47ForeignReceipts : List ForeignSourceReceipt
round47ForeignReceipts =
  fangCAS ∷
  fangDomesticPress ∷
  yanSCMP ∷
  fangSCMP ∷
  chinaNineComparison ∷
  wangDanhauChinaEmbassy ∷
  []

round47ForeignReceiptCount : Nat
round47ForeignReceiptCount = 6

foreignReportingCanCorroborateIdentityEventAndTechnicalRole : Bool
foreignReportingCanCorroborateIdentityEventAndTechnicalRole = true

foreignReportingCannotPayH2 : Bool
foreignReportingCannotPayH2 = true

foreignReportingCannotPayH3 : Bool
foreignReportingCannotPayH3 = true

clusterNarrativeCannotOverrideObjectEvidence : Bool
clusterNarrativeCannotOverrideObjectEvidence = true

crossJurisdictionAgreementDoesNotCreateIndependenceAutomatically : Bool
crossJurisdictionAgreementDoesNotCreateIndependenceAutomatically = true

institutionalObituaryAndPressReportMustRemainDistinctSourceRoles : Bool
institutionalObituaryAndPressReportMustRemainDistinctSourceRoles = true

foreignSourceAbsenceCannotPayConcealment : Bool
foreignSourceAbsenceCannotPayConcealment = true

round47H2PaidCount : Nat
round47H2PaidCount = 0

round47H3PaidCount : Nat
round47H3PaidCount = 0

round47Narrative : String
round47Narrative = "Chinese domestic institutional records, Hong Kong reporting and other non-US reporting independently preserve useful local facts about several cases and show that the scientist-loss pattern is discussed outside the United States. The strongest foreign-source payment is event/object corroboration and external salience. These sources do not presently establish a shared programme, hostile mechanism, common cause, or formal Chinese-government inquiry into the nine-person cluster."
