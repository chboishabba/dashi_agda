module DASHI.Culture.MissingDeceasedTwentyScientistRound28AmyNASACandidateWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 28: AMY -> NASA PAPER CANDIDATE WELD
--
-- Amy's archived 2020 statement says that an unnamed paper based on work by an
-- unnamed member of her team while a NASA MSFC civil servant was under NASA
-- review.  NASA NTRS now gives us a concrete later-public Technical Memorandum:
-- TM 20205010911 by R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld, recording
-- MSFC work under SAA8-1519855.  The chronology and institutional coordinates
-- make this a high-value candidate; they do not by themselves identify Amy's
-- unnamed paper with the NASA memorandum.
------------------------------------------------------------------------

record AmyNASAPaperCandidateWeld : Set where
  constructor amy-nasa-paper-candidate-weld
  field
    amyStatementSource : Attribution.AttributedSource
    nasaTechnicalMemorandumSource : Attribution.AttributedSource
    nasaAgreementSource : Attribution.AttributedSource
    amyStatementNASAReviewClaimPaid : Bool
    nasaTM20205010911PrimaryPaid : Bool
    nasaSAA81519855Paid : Bool
    timelineCompatibilityPaid : Bool
    msfcOriginCompatibilityPaid : Bool
    broadTechnicalCompatibilityPaid : Bool
    exactReportIdentityPaid : Bool
    teamMemberIdentityPaid : Bool
    candidateReportNamesAmy : Bool
    sameObjectSemanticsPaid : Bool
    candidatePays : String
    candidateDoesNotPay : String
    nextLiteralPayment : String

open AmyNASAPaperCandidateWeld public

amy2020StatementSource : Attribution.AttributedSource
amy2020StatementSource = Attribution.mkNoDOISource
  "Amy Eskridge statement, preserved in later archived reproductions"
  "September 2020 statement concerning unnamed NASA-reviewed paper"
  "archived social-media / conference-message reproduction; underlying statement remains self-report"
  "2020"
  "https://archive.ph/O3Pgg"
  Attribution.archivalSource
  "pays the bounded proposition that the reproduced statement attributes to Amy: foundational work by an unnamed team member while at NASA MSFC, subsequently matured by The Institute, with an unnamed paper said to be under NASA review"
  Attribution.publicAttribution

amy2020StatementSnowball : Snowball.SourceRoleSnowballReceipt amy2020StatementSource
amy2020StatementSnowball = Snowball.canonicalSourceRoleSnowballReceipt amy2020StatementSource

nasaTMSource : Attribution.AttributedSource
nasaTMSource = Attribution.mkNoDOISource
  "R. H. Eskridge; M. A. Nelson; M. P. Schoenfeld"
  "A Study of the Pope-Osborne Angular Momentum Synthesis Theory (POAMS) Including a Mathematical Reformulation and Validation Experiment"
  "NASA Technical Memorandum 20205010911; Marshall Space Flight Center"
  "2021"
  "https://ntrs.nasa.gov/citations/20205010911"
  Attribution.governmentSource
  "primary NASA source paying the identity, authors, MSFC provenance, acquisition/publication dates, SAA8-1519855 relationship and bounded preliminary-result language of the candidate technical memorandum"
  Attribution.publicAttribution

nasaTMSnowball : Snowball.SourceRoleSnowballReceipt nasaTMSource
nasaTMSnowball = Snowball.canonicalSourceRoleSnowballReceipt nasaTMSource

nasaAgreementSource : Attribution.AttributedSource
nasaAgreementSource = Attribution.mkNoDOISource
  "National Aeronautics and Space Administration"
  "List of Active Space Act Agreements as of December 31, 2016"
  "NASA released active domestic private-sector SAA list"
  "2016"
  "https://searchpub.nssc.nasa.gov/servlet/sm.web.Fetch/Active%20Domestic%20Private%20Sector%20SAAs%20as%20of%20%2012-31-2016.pdf?did=1848490&rhid=1000&type=released"
  Attribution.governmentSource
  "primary agreement-index surface paying Quantum Machines LLC, Advanced Propulsion Theory and Experimentation, MSFC, and SAA8-1519855 with its 2015-2020 period"
  Attribution.publicAttribution

nasaAgreementSnowball : Snowball.SourceRoleSnowballReceipt nasaAgreementSource
nasaAgreementSnowball = Snowball.canonicalSourceRoleSnowballReceipt nasaAgreementSource

amyNASACandidate : AmyNASAPaperCandidateWeld
amyNASACandidate = amy-nasa-paper-candidate-weld
  amy2020StatementSource
  nasaTMSource
  nasaAgreementSource
  true
  true
  true
  true
  true
  true
  false
  false
  false
  false
  "an exact public NASA technical memorandum, an exact Space Act Agreement, MSFC provenance, and chronology compatible with Amy's reported September 2020 review statement"
  "identity of Amy's unnamed paper, identity of the unnamed team member, Amy authorship or participation in TM 20205010911, Institute participation in SAA8-1519855, H2, H3, suppression, or causal linkage"
  "recover the original September-2020 message/email or NASA release/IP-review receipt containing a title, authors, report identifier, SAA number, POAMS/V3 identifier or other literal same-object coordinate linking Amy's statement to TM 20205010911"

amyStatementNASAReviewClaimPaid : Bool
amyStatementNASAReviewClaimPaid = true

nasaTM20205010911PrimaryPaid : Bool
nasaTM20205010911PrimaryPaid = true

nasaSAA81519855Paid : Bool
nasaSAA81519855Paid = true

timelineCompatibilityPaid : Bool
timelineCompatibilityPaid = true

exactReportIdentityPaid : Bool
exactReportIdentityPaid = false

teamMemberIdentityPaid : Bool
teamMemberIdentityPaid = false

candidateReportNamesAmy : Bool
candidateReportNamesAmy = false

sameObjectSemanticsPaid : Bool
sameObjectSemanticsPaid = false

publicationAfterStatementCannotPayIdentity : Bool
publicationAfterStatementCannotPayIdentity = true

timelineCompatibilityCannotPaySameObject : Bool
timelineCompatibilityCannotPaySameObject = true

sharedInstitutionCannotNameUnnamedTeamMember : Bool
sharedInstitutionCannotNameUnnamedTeamMember = true

candidateTechnicalSimilarityCannotPayPaperIdentity : Bool
candidateTechnicalSimilarityCannotPayPaperIdentity = true

round28H2PaidCount : Nat
round28H2PaidCount = 0

round28H3PaidCount : Nat
round28H3PaidCount = 0

round28Pareto : String
round28Pareto = "The Amy technical-object debt has narrowed from 'find the paper' to 'identify Amy's unnamed 2020 NASA-reviewed paper'. TM 20205010911 and SAA8-1519855 are now exact primary candidate coordinates, but literal paper identity and unnamed-team-member identity remain unpaid. Highest-alpha acquisition is the original 2020 email/message or NASA IP/public-release transaction containing a title, author, report number, SAA number, POAMS/V3 identifier or equivalent same-object key."