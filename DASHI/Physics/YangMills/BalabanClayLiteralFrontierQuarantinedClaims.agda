module DASHI.Physics.YangMills.BalabanClayLiteralFrontierQuarantinedClaims where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Fail-closed provenance quarantine.
--
-- These entries are NOT literature authorities and are NOT imported by any
-- theorem producer.  They record public completion claims encountered during
-- the provenance audit so that a future contributor cannot accidentally cite a
-- claimed Millennium solution as an established premise.
--
-- Quarantine is not a mathematical refutation.  It means only that the item is
-- self-published/unrefereed, makes a completion-level claim, and has not been
-- independently reduced to the repository's exact theorem interfaces.
------------------------------------------------------------------------

data ProvenanceTier : Set where
  peerReviewedPrimary establishedExpository moderatedPreprint
    unreviewedCandidate quarantinedCompletionClaim : ProvenanceTier

record QuarantinedClaim : Set where
  constructor quarantined
  field
    authorOrSite : String
    claimedTitleOrScope : String
    repositoryOrVenue : String
    stableIdentifier : String
    reviewStatus : String
    tier : ProvenanceTier
    admissibleAsAuthority : Bool
    reasonForQuarantine : String
    admissibleFutureUse : String

open QuarantinedClaim public

yangmillsDevClaim : QuarantinedClaim
yangmillsDevClaim = quarantined
  "Oliver Odusanya / yangmills.dev"
  "Website claim: Yang--Mills Mass Gap -- Proof Complete"
  "Personal domain"
  "yangmills.dev"
  "Self-published completion claim; no peer-reviewed publication established by the audit"
  quarantinedCompletionClaim
  false
  "Marketing-style completion and bespoke-verification claims cannot supply mathematical premises"
  "A concrete formula may be copied only into an independently proved falsification test"

zenodoMassGapClaim : QuarantinedClaim
zenodoMassGapClaim = quarantined
  "Harold D. Kirk"
  "From Lattice Mass Gap to Continuum SU(2) Yang--Mills"
  "Zenodo"
  "10.5281/zenodo.18824739"
  "Repository deposit; no peer-reviewed status established by the audit"
  quarantinedCompletionClaim
  false
  "Claims completion of continuum/OS/mass-gap steps of an open Millennium problem"
  "May be inspected as an unreviewed candidate, never imported as an authority"

zenodoMassGapNontrivialityCandidate : QuarantinedClaim
zenodoMassGapNontrivialityCandidate = quarantined
  "Harold D. Kirk"
  "Mass Gap and Nontriviality for Four-Dimensional Yang--Mills via Lattice Coercivity and a Symmetry-Forced Haar Measure"
  "Zenodo preprint, version 2.0, 16 April 2026"
  "10.5281/zenodo.19614728"
  "Self-published repository preprint; the record itself states that uniqueness is not claimed and that BRST extension is discussed but not verified"
  quarantinedCompletionClaim
  false
  "Claims OS axioms, O(4) invariance, positive mass gap and non-Gaussianity for an unreviewed candidate addressing Clay requirements"
  "Specific lattice inequalities may enter only as independently reconstructed falsification targets"

vixraErikssonCorpus : QuarantinedClaim
vixraErikssonCorpus = quarantined
  "Lluis Eriksson"
  "Multi-preprint Balaban/Yang--Mills completion corpus"
  "viXra"
  "reported 2026 corpus"
  "Unmoderated repository; completion claims superseded or revised within the corpus"
  quarantinedCompletionClaim
  false
  "No editorial or moderation gate and no independent proof receipt"
  "Individual estimates require independent derivation and convention checking"

preprintsOrgCompletionClaims : QuarantinedClaim
preprintsOrgCompletionClaims = quarantined
  "Various authors"
  "Yang--Mills impossibility/completion submissions"
  "Preprints.org"
  "including manuscript 202504.1268"
  "Unrefereed preprint-hosting submission"
  quarantinedCompletionClaim
  false
  "Completion-level claims lack an accepted proof and cannot calibrate DASHI constants"
  "Specific finite identities may be separately audited"

academiaEduCompletionClaims : QuarantinedClaim
academiaEduCompletionClaims = quarantined
  "Various authors"
  "Unconditional Yang--Mills solution uploads"
  "Academia.edu"
  "provenance-audit cluster"
  "Author-upload platform; no publication or review status established"
  quarantinedCompletionClaim
  false
  "Platform presence does not establish mathematical review or correctness"
  "No theorem dependency is permitted"

cambridgeEngageAgawaClaim : QuarantinedClaim
cambridgeEngageAgawaClaim = quarantined
  "Agawa"
  "Claimed rigorous Yang--Mills mass-gap proof"
  "Cambridge Open Engage"
  "provenance-audit candidate"
  "Preprint platform; no accepted peer-reviewed proof established"
  quarantinedCompletionClaim
  false
  "Completion claim remains external to the recognized proof literature"
  "Can only motivate independently stated test obligations"

arxivJacobsenCompletionClaim : QuarantinedClaim
arxivJacobsenCompletionClaim = quarantined
  "D. C. Jacobsen"
  "Claimed constructive SU(3) Yang--Mills proof"
  "arXiv"
  "provenance-audit candidate"
  "Moderated preprint venue, but completion claim is unrefereed and unaccepted"
  quarantinedCompletionClaim
  false
  "arXiv moderation is not peer review and does not settle a Millennium problem"
  "Individual lemmas may be evaluated only after exact independent reconstruction"

quarantinedCompletionClaims : List QuarantinedClaim
quarantinedCompletionClaims =
  yangmillsDevClaim ∷
  zenodoMassGapClaim ∷
  zenodoMassGapNontrivialityCandidate ∷
  vixraErikssonCorpus ∷
  preprintsOrgCompletionClaims ∷
  academiaEduCompletionClaims ∷
  cambridgeEngageAgawaClaim ∷
  arxivJacobsenCompletionClaim ∷ []
