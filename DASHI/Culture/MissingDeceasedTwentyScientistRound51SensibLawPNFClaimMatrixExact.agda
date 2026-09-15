module DASHI.Culture.MissingDeceasedTwentyScientistRound51SensibLawPNFClaimMatrixExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Culture.MissingDeceasedTwentyScientistRound50ProfessionalEvidenceRoomExact as R50
import DASHI.Culture.MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact as R44
import DASHI.Culture.MissingDeceasedTwentyScientistRound49SourceOriginIndependenceAuditExact as R49
import DASHI.Cognition.PNF.SensibLawWrongTypeDownstreamPrimarySourceDisciplineExact as SourceDiscipline
import DASHI.Cognition.PNF.SensibLawCullenResidualAdmissionBidiExact as ResidualAdmission
import DASHI.Core.EvidenceReliabilityPolarityExact as Polarity

------------------------------------------------------------------------
-- ROUND 51: SENSIBLAW / PNF CLAIM-SOURCE MATRIX
--
-- The professional evidence room from Round 50 is refined using two existing
-- SensibLaw/PNF ideas:
--
--   1. primary-source discipline persists through every downstream decision
--      stage; one upstream source does not silently pay later stages;
--   2. a discovered discriminator/residual cannot be installed into a consumer
--      until its exact source, applicability/authority context and target
--      element are welded together.
--
-- Applied here generically, without pretending that this investigation is
-- already a legal cause of action or that PNF classification creates facts.
------------------------------------------------------------------------

data ClaimStage : Set where
  identityStage : ClaimStage
  eventStage : ClaimStage
  technicalRoleStage : ClaimStage
  exactObjectStage : ClaimStage
  crossPersonObjectStage : ClaimStage
  officialConcernStage : ClaimStage
  causalMechanismStage : ClaimStage
  targetingStage : ClaimStage
  legalCharacterisationStage : ClaimStage
  publicationStage : ClaimStage


data ClaimDisposition : Set where
  paidSupport : ClaimDisposition
  paidOpposition : ClaimDisposition
  paidConflict : ClaimDisposition
  unresolvedIgnorance : ClaimDisposition
  leadOnly : ClaimDisposition
  sourceRoleBlocked : ClaimDisposition
  authorityBlocked : ClaimDisposition
  coverageBlocked : ClaimDisposition

record ProfessionalResidual : Set where
  constructor professional-residual
  field
    residualId : String
    missingCoordinate : String
    whyCurrentEvidenceCannotPay : String
    nextDiscriminatingAcquisition : String
    investigatorDebt : String
    lawyerDebt : String
    journalistDebt : String

open ProfessionalResidual public

record ClaimSourceMatrixRow : Set where
  constructor claim-source-matrix-row
  field
    claimId : String
    proposition : String
    stage : ClaimStage
    sourceReferences : String
    sourceRole : String
    sourceOriginStatus : String
    independenceStatus : String
    reliabilityStatus : String
    disposition : ClaimDisposition
    investigatorStatus : String
    lawyerStatus : String
    journalistStatus : String
    legalCharacterisationStatus : String
    pnfConsumerReference : String
    residual : ProfessionalResidual
    promotionReference : String

open ClaimSourceMatrixRow public

------------------------------------------------------------------------
-- 1. Reza / McCasland HCB.
------------------------------------------------------------------------

rezaMcCaslandResidual : ProfessionalResidual
rezaMcCaslandResidual = professional-residual
  "R51-HCB-XPERSON"
  "identity-bearing contemporaneous McCasland receipt on the same exact HCB/Mondaloy contract/task/object as Monica Jacinto/Reza"
  "Monica has an exact HBTD/Mondaloy project role and McCasland has a personal HCB programme reference, but current evidence remains cross-granular rather than same-object."
  "Acquire 2011-2013 HCB programme review, contract modification, materials approval, attendee/distribution roster, task order or proceedings record that names McCasland on FA9300-07-C-0001 / Mondaloy / the exact HBTD task."
  "Keep linked-subcluster and common-programme hypotheses live; do not promote without literal same-object receipt."
  "Authentication and proposition-purpose analysis remain item-specific; no legal wrongdoing/causation proposition is presently offered or paid."
  "Publishable formulation may state the two separately paid role surfaces and unresolved same-object question; must not collapse them into one proven task."

rezaMcCaslandHCBRow : ClaimSourceMatrixRow
rezaMcCaslandHCBRow = claim-source-matrix-row
  "CLAIM-HCB-01"
  "Monica Jacinto/Reza and Neil McCasland participated in the same exact HCB/Mondaloy technical object."
  crossPersonObjectStage
  "R31-R39 exact HCB contract/project/programme surfaces"
  "mixed exact project-role + personal programme-reference source roles"
  "multiple primary/near-primary and derivative surfaces retained separately"
  "source-origin dependence audited; no republication counted as independent payment"
  "strong single-person support but missing literal cross-person weld"
  unresolvedIgnorance
  "highest-alpha H2 acquisition leaf"
  "not presently framed as a litigated legal proposition; exact source and jurisdiction-specific admissibility would be separate downstream work"
  "not publishable as established same-object fact; publishable only as unresolved overlap question with source-role distinction"
  "no WrongType/liability classification paid"
  "crossPersonObject consumer requires exact retained-person same-object coordinate"
  rezaMcCaslandResidual
  "H2 remains unpaid"

------------------------------------------------------------------------
-- 2. Chinese nine-person cluster provenance.
------------------------------------------------------------------------

chineseClusterResidual : ProfessionalResidual
chineseClusterResidual = professional-residual
  "R51-CHINA-ORIGIN"
  "first-publication/source-origin graph for the nine-person cluster narrative"
  "The nine-person comparison set is externally assembled, but multiple outlet publication has not been shown to arise from independent provenance roots."
  "Trace earliest cluster publication, source-of-source citations, syndication/republication paths and independently originated list construction."
  "Treat cluster narrative as one or more unresolved provenance families; keep individual institutional case records separately paid."
  "No legal conclusion follows from cluster repetition; source authenticity and proposition purpose must remain item-specific."
  "Any publication claiming independent corroboration must disclose current origin uncertainty and distinguish cluster assembly from individually verified deaths/roles."

chineseClusterProvenanceRow : ClaimSourceMatrixRow
chineseClusterProvenanceRow = claim-source-matrix-row
  "CLAIM-CHINA-CLUSTER-01"
  "Multiple independent outlets separately assembled the same nine-person Chinese scientist-death cluster."
  officialConcernStage
  "India Today + NewsNation + upstream Chinese/Hong Kong individual-case sources"
  "comparative reporting layered over institutional/domestic/HK case reporting"
  "Round 49 source-origin audit"
  "independence unresolved"
  "individual cases often strongly paid; independent cluster assembly not paid"
  sourceRoleBlocked
  "origin-tracing task open"
  "not a legal element and not evidence of wrongdoing merely because multiple outlets repeat the cluster"
  "publication can state externally assembled cluster; cannot state independent multi-origin corroboration yet"
  "no legal characterisation paid"
  "provenance-origin consumer requires source-root separation"
  chineseClusterResidual
  "external assembly paid; independent assembly unpaid"

------------------------------------------------------------------------
-- 3. Casias / Garcia employment-security claims.
------------------------------------------------------------------------

casiasGarciaResidual : ProfessionalResidual
casiasGarciaResidual = professional-residual
  "R51-US10-ROLE"
  "primary identity-bearing employment/role/clearance records for Casias and Garcia"
  "Primary disappearance/death records pay event identity, while stronger employment/security-role claims remain partly dependent on secondary/anonymous reporting."
  "Acquire employer, facility, contract, personnel, public-record, obituary, professional profile or other primary role carrier tied to the exact person."
  "Keep event identity and technical/security role as separate claims; do not let official inquiry context transfer role proof."
  "Authentication, hearsay/source-role and jurisdiction-specific use remain open; anonymous-source claims are leads, not automatically admissible proof."
  "Attribution must distinguish official event record from reported employment/security claims; right of reply/source verification applies where feasible."

casiasGarciaEmploymentRow : ClaimSourceMatrixRow
casiasGarciaEmploymentRow = claim-source-matrix-row
  "CLAIM-US10-ROLE-01"
  "Melissa Casias and Steven Abel Garcia held the sensitive technical/employment roles attributed to them in reporting underlying the public cohort."
  technicalRoleStage
  "New Mexico event records + congressionally cited reporting"
  "primary event record + secondary/anonymous stronger role reporting"
  "source roles explicitly separated"
  "strong event identity; weaker role provenance"
  "mixed"
  sourceRoleBlocked
  "primary role weld acquisition open"
  "role proposition not yet paid to a litigation-specific admissibility/authority standard"
  "report role claims as attributed/unconfirmed unless primary weld is obtained"
  "no WrongType/liability classification paid"
  "technicalRole consumer requires same-person primary role carrier"
  casiasGarciaResidual
  "event identity paid; stronger technical/security role not fully paid"

------------------------------------------------------------------------
-- 4. Congressional inquiry.
------------------------------------------------------------------------

congressResidual : ProfessionalResidual
congressResidual = professional-residual
  "R51-CONGRESS-SCOPE"
  "distinguish official inquiry existence/scope from truth of allegations under inquiry"
  "Primary House records establish official concern and requests for agency information, but cannot pay the underlying shared-programme, targeting or causal propositions."
  "Acquire subsequent agency responses, committee follow-up, hearings, findings or closure records as they become public; bind each to the proposition actually stated."
  "Use inquiry as context coordinate G only; do not route it into H2/H3."
  "A congressional letter may be authentic evidence that Congress acted or said X; it does not automatically prove X's underlying factual truth."
  "Publish the inquiry as official action with explicit distinction between allegation, committee concern, agency response and established fact."

congressionalInquiryRow : ClaimSourceMatrixRow
congressionalInquiryRow = claim-source-matrix-row
  "CLAIM-CONGRESS-01"
  "The U.S. House Oversight Committee formally opened an inquiry into the reported scientist death/disappearance pattern."
  officialConcernStage
  "April 20, 2026 House Oversight release and letters"
  "primary official congressional records"
  "direct official source"
  "independent of downstream media repetition for the proposition that the inquiry exists"
  "high"
  paidSupport
  "context coordinate G paid"
  "authentic primary official record for existence/scope of congressional action; underlying allegations remain separate propositions"
  "publishable as official inquiry fact with scope and caveats"
  "official concern is not legal liability, wrongdoing or causation"
  "officialConcern consumer only"
  congressResidual
  "G paid; H2/H3 unpaid"

------------------------------------------------------------------------
-- SensibLaw / PNF cross-pollinated boundaries.
------------------------------------------------------------------------

oneSourceCannotPayAllClaimStages : Bool
oneSourceCannotPayAllClaimStages = true

sourceAttachmentDoesNotCreateAuthority : Bool
sourceAttachmentDoesNotCreateAuthority = true

wrongTypeOrClassificationDoesNotDetermineDisposition : Bool
wrongTypeOrClassificationDoesNotDetermineDisposition = true

unpaidResidualMustRemainVisible : Bool
unpaidResidualMustRemainVisible = true

consumerSpecificGateCannotRewriteNativeEvidence : Bool
consumerSpecificGateCannotRewriteNativeEvidence = true

exactSourceFactDoesNotAutomaticallyPayReconstructedNarrative : Bool
exactSourceFactDoesNotAutomaticallyPayReconstructedNarrative = true

legalAuthorityDoesNotDetermineHistoricalTruth : Bool
legalAuthorityDoesNotDetermineHistoricalTruth = true

publicationReadinessDoesNotDetermineLegalAdmissibility : Bool
publicationReadinessDoesNotDetermineLegalAdmissibility = true

investigativeDiscriminatorDoesNotInstallItselfWithoutSourceWeld : Bool
investigativeDiscriminatorDoesNotInstallItselfWithoutSourceWeld = true

reliabilityAndPolarityRemainDistinct : Bool
reliabilityAndPolarityRemainDistinct = true

------------------------------------------------------------------------
-- Current matrix state.
------------------------------------------------------------------------

round51MatrixRowCount : Nat
round51MatrixRowCount = 4

round51H2PaidCount : Nat
round51H2PaidCount = 0

round51H3PaidCount : Nat
round51H3PaidCount = 0

round51Reading : String
round51Reading = "The evidence room is now claim-stage typed. A professional consumer never receives a bare source list: each proposition carries its exact stage, source role/origin, independence, reliability, evidence disposition, consumer-specific status, unpaid residual and next discriminating acquisition. This reuses SensibLaw's rule that primary-source discipline persists through downstream stages and PNF's rule that a discriminator/residual is not installed until the exact source and consumer target are welded. One source cannot pay identity, technical role, shared object, causation, targeting, legal characterisation and publication all at once."

round51Pareto : String
round51Pareto = "Next expand the four-row matrix across the 20-person frontier, but only where doing so changes a live consumer decision. Highest value remains: exact McCasland HCB same-object receipt; primary Casias/Garcia technical-role welds; source-origin graph for the Chinese cluster; and subsequent primary congressional/agency responses. Preserve individual-case facts even when a broader cluster narrative is downgraded."
