module DASHI.Physics.YangMills.BalabanClayMassGapClaimEcosystemQuarantineExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Risk audit.
--
-- The supplied research brief identified a dense cluster of recent unreviewed
-- documents claiming complete or near-complete Yang--Mills existence/mass-gap
-- proofs. No such document is treated as theorem authority here. Individual
-- finite lemmas may be extracted only after independent proof and primary-source
-- normalization inside DASHI.
------------------------------------------------------------------------

record ClaimedSolutionRiskEntry : Set where
  constructor claimedSolutionRisk
  field
    authorsOrSite : String
    titleOrScope : String
    venue : String
    stableIdentifier : String
    peerReviewVerified : Bool
    admissibleAsAuthority : Bool
    isolatedLemmaMiningPermitted : Bool
    requiredIndependentCheck : String

open ClaimedSolutionRiskEntry public

recentClaimCluster : ClaimedSolutionRiskEntry
recentClaimCluster = claimedSolutionRisk
  "multiple authors/sites; metadata varies"
  "complete or near-complete four-dimensional Yang--Mills existence and mass-gap claims"
  "unreviewed preprints, personal sites and document repositories"
  "representative locator arXiv:2506.00284; adjacent 2026 claims logged separately"
  false
  false
  true
  "reprove each extracted lemma in the selected DASHI convention; never import a global completion claim"

standingQuarantineRule : String
standingQuarantineRule =
  "A claimed complete solution contributes no theorem premise. Only isolated, independently checkable mechanisms may enter a typed conditional cutset."

quarantinedClaimEntries : List ClaimedSolutionRiskEntry
quarantinedClaimEntries = recentClaimCluster ∷ []

claimEcosystemAuditLevel : ProofLevel
claimEcosystemAuditLevel = machineChecked

-- The Boolean authority field above carries the quarantine decision.  At the
-- proof-level layer, an unaccepted completion claim is an open/conjectural item,
-- not a separate constructor.
claimedCompleteProofsAcceptedAsAuthority : ProofLevel
claimedCompleteProofsAcceptedAsAuthority = conjectural

independentLemmaReproductionInputsLevel : ProofLevel
independentLemmaReproductionInputsLevel = conditional
