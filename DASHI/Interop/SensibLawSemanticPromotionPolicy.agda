module DASHI.Interop.SensibLawSemanticPromotionPolicy where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Algebra.TetralemmaBridge using
  ( TetralemmaPosition
  ; affirmation
  ; negation
  ; both
  ; neither
  )
open import DASHI.Core.AuthorityNonPromotionCore using
  ( AuthorityNonPromotionBundle
  ; mkClosedAuthorityNonPromotionBundle
  ; truthAuthorityFlag
  ; legalAuthorityFlag
  ; promotesAnyAuthority
  )

------------------------------------------------------------------------
-- SensibLaw / ITIR semantic promotion policy.
--
-- Runtime parsers may emit structural evidence and bounded heuristic hints.
-- Canonical semantic promotion depends only on the structural evidence bits.
-- Heuristic evidence is retained for audit/review but is definitionally unable
-- to alter the promoted tetralemma position.

------------------------------------------------------------------------
-- Candidate basis remains a small orthogonal carrier.  It is descriptive:
-- promotion is computed from structural evidence, never from the basis label.

data CandidateBasis : Set where
  structural : CandidateBasis
  heuristic : CandidateBasis
  mixed : CandidateBasis

record SemanticCandidate : Set where
  constructor semanticCandidate
  field
    basis : CandidateBasis
    structuralFor : Bool
    structuralAgainst : Bool
    heuristicFor : Bool
    heuristicAgainst : Bool
    targetComponent : String
    provenance : String

open SemanticCandidate public

------------------------------------------------------------------------
-- Central four-corner promotion gate.

promoteStructural : Bool → Bool → TetralemmaPosition
promoteStructural true false = affirmation
promoteStructural false true = negation
promoteStructural true true = both
promoteStructural false false = neither

promote : SemanticCandidate → TetralemmaPosition
promote candidate =
  promoteStructural
    (structuralFor candidate)
    (structuralAgainst candidate)

------------------------------------------------------------------------
-- Canonical constructors for the three runtime candidate classes.

structuralCandidate :
  Bool → Bool → String → String → SemanticCandidate
structuralCandidate for against target source =
  semanticCandidate
    structural
    for
    against
    false
    false
    target
    source

heuristicCandidate :
  Bool → Bool → String → String → SemanticCandidate
heuristicCandidate for against target source =
  semanticCandidate
    heuristic
    false
    false
    for
    against
    target
    source

mixedCandidate :
  Bool → Bool → Bool → Bool → String → String → SemanticCandidate
mixedCandidate structural-for structural-against heuristic-for heuristic-against target source =
  semanticCandidate
    mixed
    structural-for
    structural-against
    heuristic-for
    heuristic-against
    target
    source

------------------------------------------------------------------------
-- Tetralemma computation laws.

structural-for-promotes-affirmation :
  promoteStructural true false ≡ affirmation
structural-for-promotes-affirmation = refl

structural-against-promotes-negation :
  promoteStructural false true ≡ negation
structural-against-promotes-negation = refl

structural-conflict-promotes-both :
  promoteStructural true true ≡ both
structural-conflict-promotes-both = refl

structural-absence-promotes-neither :
  promoteStructural false false ≡ neither
structural-absence-promotes-neither = refl

------------------------------------------------------------------------
-- Heuristic quarantine laws.

heuristic-only-abstains :
  ∀ heuristic-for heuristic-against target source →
  promote (heuristicCandidate heuristic-for heuristic-against target source)
  ≡ neither
heuristic-only-abstains heuristic-for heuristic-against target source = refl

promotion-ignores-heuristic-bits :
  ∀ structural-for structural-against
    heuristic-for₁ heuristic-against₁
    heuristic-for₂ heuristic-against₂
    target source →
  promote
    (mixedCandidate
      structural-for structural-against
      heuristic-for₁ heuristic-against₁
      target source)
  ≡
  promote
    (mixedCandidate
      structural-for structural-against
      heuristic-for₂ heuristic-against₂
      target source)
promotion-ignores-heuristic-bits true true hF₁ hA₁ hF₂ hA₂ target source = refl
promotion-ignores-heuristic-bits true false hF₁ hA₁ hF₂ hA₂ target source = refl
promotion-ignores-heuristic-bits false true hF₁ hA₁ hF₂ hA₂ target source = refl
promotion-ignores-heuristic-bits false false hF₁ hA₁ hF₂ hA₂ target source = refl

mixed-without-structural-support-abstains :
  ∀ heuristic-for heuristic-against target source →
  promote
    (mixedCandidate
      false false
      heuristic-for heuristic-against
      target source)
  ≡ neither
mixed-without-structural-support-abstains heuristic-for heuristic-against target source = refl

------------------------------------------------------------------------
-- Closed authority boundary.
--
-- The gate classifies evidence position only.  It does not itself confer
-- truth, legal, admissibility, runtime, or external authority.

semanticPromotionAuthorityBoundary : AuthorityNonPromotionBundle
semanticPromotionAuthorityBoundary =
  mkClosedAuthorityNonPromotionBundle
    "SensibLaw semantic promotion gate classifies structural evidence without conferring authority"

semantic-promotion-truth-authority-closed :
  truthAuthorityFlag semanticPromotionAuthorityBoundary ≡ false
semantic-promotion-truth-authority-closed = refl

semantic-promotion-legal-authority-closed :
  legalAuthorityFlag semanticPromotionAuthorityBoundary ≡ false
semantic-promotion-legal-authority-closed = refl

semantic-promotion-all-authority-closed :
  promotesAnyAuthority semanticPromotionAuthorityBoundary ≡ false
semantic-promotion-all-authority-closed = refl

------------------------------------------------------------------------
-- Exported policy surface.

record SemanticPromotionPolicySurface : Set₁ where
  field
    candidateCarrier : Set
    positionCarrier : Set
    centralPromotion : SemanticCandidate → TetralemmaPosition
    heuristicOnlyAbstains :
      ∀ heuristic-for heuristic-against target source →
      centralPromotion
        (heuristicCandidate heuristic-for heuristic-against target source)
      ≡ neither
    heuristicBitsAreNonPromoting :
      ∀ structural-for structural-against
        heuristic-for₁ heuristic-against₁
        heuristic-for₂ heuristic-against₂
        target source →
      centralPromotion
        (mixedCandidate
          structural-for structural-against
          heuristic-for₁ heuristic-against₁
          target source)
      ≡
      centralPromotion
        (mixedCandidate
          structural-for structural-against
          heuristic-for₂ heuristic-against₂
          target source)
    authorityBoundary : AuthorityNonPromotionBundle
    nonClaimBoundary : List String

semanticPromotionPolicySurface : SemanticPromotionPolicySurface
semanticPromotionPolicySurface =
  record
    { candidateCarrier = SemanticCandidate
    ; positionCarrier = TetralemmaPosition
    ; centralPromotion = promote
    ; heuristicOnlyAbstains = heuristic-only-abstains
    ; heuristicBitsAreNonPromoting = promotion-ignores-heuristic-bits
    ; authorityBoundary = semanticPromotionAuthorityBoundary
    ; nonClaimBoundary =
        "The gate consumes typed candidate evidence; it does not parse text or import spaCy"
        ∷ "Surface-form, regex, overlap, and lexical hints may be retained only in heuristic evidence fields"
        ∷ "Heuristic evidence is definitionally ignored by canonical promotion"
        ∷ "Affirmation, negation, both, and neither classify evidence position; they do not establish legal truth"
        ∷ "Authority remains closed unless a separate accepted domain artifact supplies it"
        ∷ []
    }
