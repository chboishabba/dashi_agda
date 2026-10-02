module DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- CHEGEN / WALSH "UNDERMETHYLATION" SOURCE ATLAS
--
-- Attribution rule:
--
--   * @danielchegenp is the creator/channel handle visible in the user-supplied
--     Reel 19 transcript capture (video id Dd2IsL9IQGH).
--   * Claims made in that reel remain claims of that creator unless the reel
--     explicitly attributes them onward.
--   * Walsh / Walsh Institute claims remain Walsh / Walsh Institute claims.
--   * Peer-reviewed biochemical sources are separately attributed.
--   * DASHI composition of those sources is DASHI synthesis and is not
--     retroactively attributed to any external speaker.
--
-- The atlas deliberately does not infer a legal/full personal name from the
-- handle @danielchegenp.
------------------------------------------------------------------------

chegenReel19 : Source.AttributedSource
chegenReel19 =
  Source.mkNoDOISource
    "@danielchegenp"
    "Reel 19: 'Are you undermethylated?'"
    "Instagram reel; user-supplied transcript capture via freescribe.app; channel ID danielchegenp; video ID Dd2IsL9IQGH"
    "2026"
    "https://www.instagram.com/reel/Dd2IsL9IQGH/"
    (Source.namedSourceKind "social-media creator source")
    "Primary source for the reel's specific phenotype-fingerprint, shared-biochemical-route, and single-capsule framing. The creator's own synthesis is retained separately from claims attributed by the creator to Walsh Institute."
    Source.publicAttribution

walshInstituteMentalHealth : Source.AttributedSource
walshInstituteMentalHealth =
  Source.mkNoDOISource
    "Walsh Research Institute"
    "Nutrients & Mental Health"
    "Walsh Research Institute"
    "accessed 2026"
    "https://www.walshinstitute.org/nutrients--mental-health.html"
    Source.institutionalSource
    "Institutional source for Walsh-program biochemical-imbalance framing. Institutional statements are not promoted to population-level causal or diagnostic authority."
    Source.publicAttribution

walshInterviewThirtyThousand : Source.AttributedSource
walshInterviewThirtyThousand =
  Source.mkNoDOISource
    "William J. Walsh; interviewed by Wendy Myers"
    "Nutrition and the Mind with Dr. William Walsh"
    "Myers Detox transcript"
    "2016"
    "https://myersdetox.com/transcript-129-nutrition-and-the-mind-with-dr-william-walsh/"
    Source.practitionerSource
    "Source in which Walsh describes evaluating approximately 30,000 patients and discusses methylation/histamine interpretations. This is a practitioner/interview source, not a conventional 30,000-participant validation study receipt."
    Source.publicAttribution

mthfrPerspective2026 : Source.AttributedSource
mthfrPerspective2026 =
  Source.mkDOISource
    "Linnea K M Blomgren; Shuning Guo; D Sean Froese; Thomas J McCorvie; Wyatt W Yue"
    "5,10-Methylenetetrahydrofolate Reductase—the Key Allosteric Regulator in One-Carbon Metabolism"
    "Biochemistry"
    "2026"
    "10.1021/acs.biochem.5c00707"
    "https://pubmed.ncbi.nlm.nih.gov/41758688/"
    Source.academicArticleSource
    "Peer-reviewed source for MTHFR placement in one-carbon metabolism, production of 5-methyl-THF, linkage to the methionine cycle, and SAM-dependent regulation. It does not establish a Walsh personality subtype."
    Source.publicAttribution

samMethyltransferases2021 : Source.AttributedSource
samMethyltransferases2021 =
  Source.mkDOISource
    "Jiaojiao Li; Chunxiao Sun; Wenwen Cai; Jing Li; Barry P. Rosen; Jian Chen"
    "Insights into S-adenosyl-l-methionine (SAM)-dependent methyltransferase related diseases and genetic polymorphisms"
    "Mutation Research / Reviews in Mutation Research"
    "2021"
    "10.1016/j.mrrev.2021.108396"
    "https://pubmed.ncbi.nlm.nih.gov/34893161/"
    Source.academicArticleSource
    "Peer-reviewed source for SAM-dependent methyltransferases including COMT, HNMT and DNMT, supporting shared methyl-donor dependence without collapsing their substrates, tissues or physiological roles."
    Source.publicAttribution

canonicalChegenWalshUndermethylationSourceAtlas :
  Source.AttributedSourceAtlas
canonicalChegenWalshUndermethylationSourceAtlas =
  Source.mkSourceAtlas
    "Chegen / Walsh undermethylation source atlas"
    "DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact"
    ( chegenReel19
    ∷ walshInstituteMentalHealth
    ∷ walshInterviewThirtyThousand
    ∷ mthfrPerspective2026
    ∷ samMethyltransferases2021
    ∷ [])
    "Separates the reel creator's claims, Walsh/Walsh-Institute claims, and peer-reviewed biochemical claims. No source attribution imports agreement, proof, endorsement, population transport, diagnosis, or treatment authority."

------------------------------------------------------------------------
-- Explicit attribution firewalls.
------------------------------------------------------------------------

data ReelCreatorClaimEqualsWalshClaim : Set where
data WalshClaimEqualsPeerReviewedFinding : Set where
data DASHISynthesisEqualsExternalSpeakerClaim : Set where
data HandleDeterminesLegalIdentity : Set where

reelCreatorClaimDoesNotCollapseIntoWalsh :
  ReelCreatorClaimEqualsWalshClaim → ⊥
reelCreatorClaimDoesNotCollapseIntoWalsh ()

walshClaimDoesNotCollapseIntoPeerReviewedFinding :
  WalshClaimEqualsPeerReviewedFinding → ⊥
walshClaimDoesNotCollapseIntoPeerReviewedFinding ()

dashiSynthesisNotAttributedBackToExternalSpeaker :
  DASHISynthesisEqualsExternalSpeakerClaim → ⊥
dashiSynthesisNotAttributedBackToExternalSpeaker ()

handleDoesNotDetermineLegalIdentity :
  HandleDeterminesLegalIdentity → ⊥
handleDoesNotDetermineLegalIdentity ()

record ReelLocator : Set where
  constructor reelLocator
  field
    creatorHandle : String
    channelId : String
    videoId : String
    transcriptCaptureReference : String
    creatorIdentityBeyondHandleVerified : Bool
    creatorIdentityBeyondHandleVerifiedIsFalse :
      creatorIdentityBeyondHandleVerified ≡ false

canonicalReel19Locator : ReelLocator
canonicalReel19Locator =
  reelLocator
    "@danielchegenp"
    "danielchegenp"
    "Dd2IsL9IQGH"
    "user-supplied freescribe.app transcript screenshot in conversation, 2026-10-02"
    false refl
