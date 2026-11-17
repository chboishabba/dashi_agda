module DASHI.Culture.AmyEskridgeVideoHAL5AllSlidesExact where

-- Every original 2018 HAL5 page, INCLUDING source families the edited video
-- omits, with exact primary document and named talk author attribution.
-- Amy Eskridge, "A Historical Perspective on Anti-Gravity Technology",
-- Huntsville Alabama L5 Society, 6 Dec 2018, PDF 35 pages:
-- https://www.hal5.org/PDF/HAL5-Dec2018-Talk-AntiGravity.pdf
-- Program: https://www.hal5.org/program-2018-12.shtml
-- Slide-to-video links are DASHI archival reconstructions, not Eskridge's
-- endorsement of Be Inspired's 2026 editorial claims.
-- Record the original false Tesla patent number as a source *claim*, then
-- compare against original US1655144A grain-treatment patent.
-- Source claim != independent physics or forensic verification.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Culture.AmyEskridgeHAL5AntigravitySourceEntitlementExact as Hal5
import DASHI.Culture.AmyEskridgeVideoClaimAttributionLedgerExact as Video

record HAL5Slide : Set where
  constructor hal5-slide
  field
    pdfPageOneBased : Nat
    summaryOfWhatSlideActuallySays : String
    editedVideoClaimsDiscussingThisSlide : List Video.RawAttributedClaim
    criticalAttributionBoundary : String
    originalPresentation : Hal5.HAL5TalkSourceReceipt
open HAL5Slide public

deck01 : HAL5Slide
deck01 = hal5-slide 1 "Title, author Amy Eskridge, Institute for Exotic Science" (Video.claim015 ∷ []) "Presenter and talk identity" Hal5.canonicalHAL5TalkSourceReceipt

deck02 : HAL5Slide
deck02 = hal5-slide 2 "Institute PBC research-scope self-description" (Video.claim013 ∷ []) "Institutional self-description; not independent programme outcome" Hal5.canonicalHAL5TalkSourceReceipt

deck03 : HAL5Slide
deck03 = hal5-slide 3 "Institute staff/team roles" ([]) "Personnel claims need exact original company/SEC documentation" Hal5.canonicalHAL5TalkSourceReceipt

deck04 : HAL5Slide
deck04 = hal5-slide 4 "Amy and Richard Eskridge roles and biographical summary" (Video.claim009 ∷ []) "Role and affiliation, no primary experimental validation" Hal5.canonicalHAL5TalkSourceReceipt

deck05 : HAL5Slide
deck05 = hal5-slide 5 "Gravity and antigravity definitions" (Video.claim020 ∷ []) "Historical definition used in video, not precise mechanism proof" Hal5.canonicalHAL5TalkSourceReceipt

deck06 : HAL5Slide
deck06 = hal5-slide 6 "Gravity historical sketch Newton/Kepler/Cavendish/Einstein" (Video.claim017 ∷ []) "Popular-level physics; check dates and scope" Hal5.canonicalHAL5TalkSourceReceipt

deck07 : HAL5Slide
deck07 = hal5-slide 7 "General-relativity and negative-mass rhetorical framing" (Video.claim017 ∷ Video.claim021 ∷ []) "Negative-mass assumptions do not establish vacuum-device feasibility" Hal5.canonicalHAL5TalkSourceReceipt

deck08 : HAL5Slide
deck08 = hal5-slide 8 "Four forces and graviton conjecture" (Video.claim018 ∷ Video.claim019 ∷ []) "Standard Model background and unresolved quantisation" Hal5.canonicalHAL5TalkSourceReceipt

deck09 : HAL5Slide
deck09 = hal5-slide 9 "Section heading: early antigravity research" ([]) "Structural context, not evidence" Hal5.canonicalHAL5TalkSourceReceipt

deck10 : HAL5Slide
deck10 = hal5-slide 10 "Brown gravitator and asserted vacuum test; 1960 patent" (Video.claim022 ∷ Video.claim023 ∷ Video.claim024 ∷ []) "US2949550 patent is not a vacuum experiment or proof of gravity modification" Hal5.canonicalHAL5TalkSourceReceipt

deck11 : HAL5Slide
deck11 = hal5-slide 11 "Section heading: Tesla space drive" ([]) "Only source heading; no independent Tesla artefact" Hal5.canonicalHAL5TalkSourceReceipt

deck12 : HAL5Slide
deck12 = hal5-slide 12 "Tesla patent 1655144 and William Lyne book cover" (Video.claim025 ∷ Video.claim026 ∷ []) "Patent is Hallgarth/Chandler grain-treatment; Lyne is a later secondary construction" Hal5.canonicalHAL5TalkSourceReceipt

deck13 : HAL5Slide
deck13 = hal5-slide 13 "Gravity Research Foundation Babson and essay prizes" (Video.claim028 ∷ Video.claim029 ∷ []) "Foundation history gives organised meeting in Jan 1949; 1948 reported in other historical summaries" Hal5.canonicalHAL5TalkSourceReceipt

deck14 : HAL5Slide
deck14 = hal5-slide 14 "Bryce DeWitt 1953 prize essay quotation" ([]) "Prize and critique attributable to DeWitt, no antigravity construction" Hal5.canonicalHAL5TalkSourceReceipt

deck15 : HAL5Slide
deck15 = hal5-slide 15 "Wright-Patterson 1956; Research Institute for Advanced Study lineage" ([]) "Assertions in HAL5 slide; original contract and RIASS-to-Skunkworks link not supplied" Hal5.canonicalHAL5TalkSourceReceipt

deck16 : HAL5Slide
deck16 = hal5-slide 16 "John Searl SEG 1946 free energy and antigravity" (Video.claim030 ∷ []) "Inventor/source-of-claim only, independent tests open" Hal5.canonicalHAL5TalkSourceReceipt

deck17 : HAL5Slide
deck17 = hal5-slide 17 "Norman Dean oscillatory drive" (Video.claim031 ∷ Video.claim032 ∷ []) "US2886976 rotary-inertia patent; isolated reactionless free-space experiment open" Hal5.canonicalHAL5TalkSourceReceipt

deck18 : HAL5Slide
deck18 = hal5-slide 18 "Henry Wallace spinning brass and kinemassic field" (Video.claim033 ∷ []) "US3626605/US3626606 patent filing evidence, no independent measured field" Hal5.canonicalHAL5TalkSourceReceipt

deck19 : HAL5Slide
deck19 = hal5-slide 19 "Eric Laithwaite 1974 gyroscope demonstrations" (Video.claim034 ∷ Video.claim035 ∷ []) "Royal Institution original lecture; classical dynamics control must remain" Hal5.canonicalHAL5TalkSourceReceipt

deck20 : HAL5Slide
deck20 = hal5-slide 20 "Section heading modern antigravity efforts" ([]) "Structural context, not evidence" Hal5.canonicalHAL5TalkSourceReceipt

deck21 : HAL5Slide
deck21 = hal5-slide 21 "Mansfield Amendment 1973 slide and black budgets inference" (Video.claim049 ∷ Video.claim050 ∷ []) "1969 Section 203 and later changes separate; no legislative antigravity classification mandate" Hal5.canonicalHAL5TalkSourceReceipt

deck22 : HAL5Slide
deck22 = hal5-slide 22 "John Hutchison anomaly and Philadelphia Experiment claims" ([]) "OMITTED from edited video; apparatus/test control burden remains" Hal5.canonicalHAL5TalkSourceReceipt

deck23 : HAL5Slide
deck23 = hal5-slide 23 "James F Woodward Mach-effect / speculative negative mass" (Video.claim051 ∷ Video.claim052 ∷ []) "Primary Woodward 1992 DOI claim; apparatus and negative mass distinct" Hal5.canonicalHAL5TalkSourceReceipt

deck24 : HAL5Slide
deck24 = hal5-slide 24 "Ning Li and Doug Torr AC Gravity theory and NASA grant" (Video.claim036 ∷ Video.claim037 ∷ Video.claim038 ∷ Video.claim039 ∷ []) "1991/1992 theory vs NASA static/rotating nulls and incomplete grant distinct" Hal5.canonicalHAL5TalkSourceReceipt

deck25 : HAL5Slide
deck25 = hal5-slide 25 "What happened to Ning Li? title slide" (Video.claim040 ∷ Video.claim041 ∷ Video.claim042 ∷ []) "Question heading is not evidence of subsequent death/suppression" Hal5.canonicalHAL5TalkSourceReceipt

deck26 : HAL5Slide
deck26 = hal5-slide 26 "Podkletnov effect; Poher claimed near-replication" (Video.claim043 ∷ Video.claim044 ∷ Video.claim047 ∷ []) "1992 0.05–0.3%, later circa 2%; 2003 Hathaway controlled null distinct" Hal5.canonicalHAL5TalkSourceReceipt

deck27 : HAL5Slide
deck27 = hal5-slide 27 "Douglas Torr, José Vargas, Timir Datta gravity-beam generator" ([]) "OMITTED from edited video; Torr/Vargas field converter patents US6891712 and US7327548" Hal5.canonicalHAL5TalkSourceReceipt

deck28 : HAL5Slide
deck28 = hal5-slide 28 "Li/Torr/Podkletnov/Modanese social-reception claims" (Video.claim045 ∷ Video.claim046 ∷ []) "Wikipedia removal/employment assertions need direct primary records" Hal5.canonicalHAL5TalkSourceReceipt

deck29 : HAL5Slide
deck29 = hal5-slide 29 "Claude Poher YBCO discharge and 2015 NASA test assertion" (Video.claim047 ∷ Video.claim048 ∷ []) "Poher own publications and NASA tests not interchangeable" Hal5.canonicalHAL5TalkSourceReceipt

deck30 : HAL5Slide
deck30 = hal5-slide 30 "Morningstar Applied Physics Paul Murad John Brandenburg claimed 7%" ([]) "OMITTED from edited video; slide claims no inspected independent 7% replication" Hal5.canonicalHAL5TalkSourceReceipt

deck31 : HAL5Slide
deck31 = hal5-slide 31 "Boeing GRASP, Podkletnov collaboration, TR-3B conjecture" (Video.claim053 ∷ Video.claim054 ∷ Video.claim055 ∷ []) "2002 Jane's account predates slide's 2014 claim; experimental aerospace endpoint open" Hal5.canonicalHAL5TalkSourceReceipt

deck32 : HAL5Slide
deck32 = hal5-slide 32 "Recent AATIP declassification heading" (Video.claim056 ∷ Video.claim057 ∷ []) "DIA 37 full response is 2022; earlier 2017 public reporting is distinct" Hal5.canonicalHAL5TalkSourceReceipt

deck33 : HAL5Slide
deck33 = hal5-slide 33 "Future research heading" ([]) "Structural context only" Hal5.canonicalHAL5TalkSourceReceipt

deck34 : HAL5Slide
deck34 = hal5-slide 34 "Testable hypotheses and funding conclusion; classified disappearance claim" (Video.claim063 ∷ []) "Source supports Amy discussing testing/funding, not disappearance/secret cause" Hal5.canonicalHAL5TalkSourceReceipt

deck35 : HAL5Slide
deck35 = hal5-slide 35 "Talk contact details and public identity" ([]) "Historical self-attribution, not factual programme/test receipt" Hal5.canonicalHAL5TalkSourceReceipt

all35HAL5Pages : List HAL5Slide
all35HAL5Pages =
  deck01 ∷
  deck02 ∷
  deck03 ∷
  deck04 ∷
  deck05 ∷
  deck06 ∷
  deck07 ∷
  deck08 ∷
  deck09 ∷
  deck10 ∷
  deck11 ∷
  deck12 ∷
  deck13 ∷
  deck14 ∷
  deck15 ∷
  deck16 ∷
  deck17 ∷
  deck18 ∷
  deck19 ∷
  deck20 ∷
  deck21 ∷
  deck22 ∷
  deck23 ∷
  deck24 ∷
  deck25 ∷
  deck26 ∷
  deck27 ∷
  deck28 ∷
  deck29 ∷
  deck30 ∷
  deck31 ∷
  deck32 ∷
  deck33 ∷
  deck34 ∷
  deck35 ∷ []

slideLength : List HAL5Slide → Nat
slideLength [] = zero
slideLength (_ ∷ xs) = suc (slideLength xs)

entireOriginalDeckCovered : slideLength all35HAL5Pages ≡ 35
entireOriginalDeckCovered = refl

-- Omitted slide families remain first-class primary-deck references.
videoOmittedHutchison : HAL5Slide
videoOmittedHutchison = deck22

videoOmittedTorrVargasDatta : HAL5Slide
videoOmittedTorrVargasDatta = deck27

videoOmittedMorningstar : HAL5Slide
videoOmittedMorningstar = deck30

-- These witnesses prove deck *coverage*, not experimental corroboration.
