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



walshSymptomsTraits2015 : Source.AttributedSource
walshSymptomsTraits2015 =
  Source.mkNoDOISource
    "William J. Walsh"
    "Symptoms & Traits: Undermethylated Depression"
    "Walsh Research Institute presentation material"
    "2015"
    "https://www.walshinstitute.org/uploads/1/7/9/9/17997321/acn_depression_pp_drwalsh__11_15.pdf"
    Source.institutionalSource
    "Walsh-authored presentation source for the reported undermethylated-depression trait list, including strong will, OCD tendencies, high accomplishment, inner tension, competitive/perfectionistic traits, addictive tendency and seasonal allergies. This is not independent replication."
    Source.publicAttribution

walshMethylationBrainDisorders : Source.AttributedSource
walshMethylationBrainDisorders =
  Source.mkNoDOISource
    "William J. Walsh"
    "Methylation and Brain Disorders"
    "Walsh Research Institute presentation material"
    "publication year not established by atlas"
    "https://www.walshinstitute.org/uploads/1/7/9/9/17997321/methylation_epigenetics_and_mental_health_by_william_walsh_phd.pdf"
    Source.institutionalSource
    "Walsh-authored presentation source reporting that methylation status was determined for approximately 30,000 patients over 30 years and advocating clinical interpretation of methylation status. It is retained as a source claim, not an independently validated cohort-design receipt."
    Source.publicAttribution

yoshikawaNakamuraYanai2019 : Source.AttributedSource
yoshikawaNakamuraYanai2019 =
  Source.mkDOISource
    "Takeo Yoshikawa; Tadaho Nakamura; Kazuhiko Yanai"
    "Histamine N-Methyltransferase in the Brain"
    "International Journal of Molecular Sciences"
    "2019"
    "10.3390/ijms20030737"
    "https://pubmed.ncbi.nlm.nih.gov/30744146/"
    Source.academicArticleSource
    "Peer-reviewed review for HNMT as a histamine-metabolising enzyme in brain and for the importance of HNMT to central histamine concentration; not evidence for a Walsh phenotype classifier."
    Source.publicAttribution

szukiewicz2024 : Source.AttributedSource
szukiewicz2024 =
  Source.mkDOISource
    "Dariusz Szukiewicz"
    "Histaminergic System Activity in the Central Nervous System: The Role in Neurodevelopmental and Neurodegenerative Disorders"
    "International Journal of Molecular Sciences"
    "2024"
    "10.3390/ijms25189859"
    "https://pubmed.ncbi.nlm.nih.gov/39337347/"
    Source.academicArticleSource
    "Peer-reviewed review for the two major histamine-metabolism routes, HNMT methylation and DAO oxidation, with compartment/context distinctions retained."
    Source.publicAttribution

goncalvesEtAl2022 : Source.AttributedSource
goncalvesEtAl2022 =
  Source.mkDOISource
    "Sandra Goncalves; Joana Nunes-Costa; Susana M Cardoso; Nuno Empadinhas; Joerg D Marugg"
    "Enzyme Promiscuity in Serotonin Biosynthesis, From Bacteria to Plants and Humans"
    "Frontiers in Microbiology"
    "2022"
    "10.3389/fmicb.2022.873555"
    "https://pubmed.ncbi.nlm.nih.gov/35495641/"
    Source.academicArticleSource
    "Peer-reviewed source for human/animal serotonin biosynthesis from tryptophan through 5-HTP to serotonin; this biosynthetic path is distinct from SAM-dependent methyltransferase clearance."
    Source.publicAttribution

daubnerLeWang2011 : Source.AttributedSource
daubnerLeWang2011 =
  Source.mkDOISource
    "S. Colette Daubner; Tiffany Le; Shanzhi Wang"
    "Tyrosine Hydroxylase and Regulation of Dopamine Synthesis"
    "Archives of Biochemistry and Biophysics"
    "2011"
    "10.1016/j.abb.2010.12.017"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3065393/"
    Source.academicArticleSource
    "Peer-reviewed review for catecholamine biosynthesis: tyrosine to L-DOPA by tyrosine hydroxylase and L-DOPA to dopamine by aromatic amino acid decarboxylase."
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
    ∷ walshSymptomsTraits2015
    ∷ walshMethylationBrainDisorders
    ∷ mthfrPerspective2026
    ∷ samMethyltransferases2021
    ∷ yoshikawaNakamuraYanai2019
    ∷ szukiewicz2024
    ∷ goncalvesEtAl2022
    ∷ daubnerLeWang2011
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
