module DASHI.Ontology.LeanWikidataIdentityBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Ontology.EpistemicTrit
open import DASHI.Ontology.LeanWikidataTheoremSurfaceBridge
import DASHI.Interop.WikidataCandidateRoleBridge as CandidateRole
import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.AuthorityNonPromotionCore as Authority

------------------------------------------------------------------------
-- Matching, Sitelinks and ExternalIds prove partial-bijection style identity
-- results under explicit functionality/injectivity constraints. Lexemes proves
-- denotation/translation results under its own model. DASHI consumes these as
-- candidate identity/semantic evidence; they are not unconditional identity
-- authority outside the source hypotheses.
------------------------------------------------------------------------

data LeanIdentityEvidenceKind : Set where
  matchingEvidence sitelinkEvidence externalIdentifierEvidence lexemeDenotationEvidence : LeanIdentityEvidenceKind

record LeanIdentityWitness : Set where
  constructor leanIdentityWitness
  field
    evidenceKind : LeanIdentityEvidenceKind
    theoremContract : LeanTheoremContract
    sourceMatched : Bool
    theoremAccepted : Bool
    sourceReferences : List String

open LeanIdentityWitness public

identityWitnessState : LeanIdentityWitness → EpistemicTrit
identityWitnessState witness =
  theoremReceiptState (theoremAccepted witness) (sourceMatched witness)

externalIdBijectionContract : LeanTheoremContract
externalIdBijectionContract = contract20

sitelinkBijectionContract : LeanTheoremContract
sitelinkBijectionContract = contract21

lexemeDenotationContract : LeanTheoremContract
lexemeDenotationContract = contract22

identityWitnessCandidateOnly : LeanIdentityWitness → Bool
identityWitnessCandidateOnly _ = true

identityWitnessTruthAuthority : LeanIdentityWitness → Bool
identityWitnessTruthAuthority _ = false

identityWitnessEditAuthority : LeanIdentityWitness → Bool
identityWitnessEditAuthority _ = false

identityWitnessCandidateOnlyTrue :
  (witness : LeanIdentityWitness) → identityWitnessCandidateOnly witness ≡ true
identityWitnessCandidateOnlyTrue witness = refl

identityWitnessTruthAuthorityFalse :
  (witness : LeanIdentityWitness) → identityWitnessTruthAuthority witness ≡ false
identityWitnessTruthAuthorityFalse witness = refl

identityWitnessEditAuthorityFalse :
  (witness : LeanIdentityWitness) → identityWitnessEditAuthority witness ≡ false
identityWitnessEditAuthorityFalse witness = refl

authorityBoundary : Authority.AuthorityNonPromotionBundle
authorityBoundary = Authority.mkClosedAuthorityNonPromotionBundle
  "James/Aristotle Wikidata identity evidence bridge"
