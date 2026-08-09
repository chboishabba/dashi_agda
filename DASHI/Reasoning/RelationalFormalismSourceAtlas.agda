module DASHI.Reasoning.RelationalFormalismSourceAtlas where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source atlas.  Each row records a bounded bridge role and an excluded
-- promotion.  Historical psychoanalytic sources are provenance, not direct
-- empirical proof of a particular person's motive.
------------------------------------------------------------------------

data IdentifierKind : Set where
  doiIdentifier noDoiRecorded : IdentifierKind

data SourceRole : Set where
  parapraxisHistoricalRole lexicalAccessRole speechErrorRole : SourceRole
  darvoResearchRole typedHyperfabricRole symbolicTransformRole : SourceRole

record SourceRecord : Set where
  constructor sourceRecord
  field
    authors title publication : String
    year : Nat
    identifierKind : IdentifierKind
    identifier : String
    role : SourceRole
    importedReading : String
    excludedPromotion : String

open SourceRecord public

freudPsychopathologySource : SourceRecord
freudPsychopathologySource = sourceRecord
  "Sigmund Freud"
  "The Psychopathology of Everyday Life"
  "S. Karger / original German publication"
  1901
  noDoiRecorded
  "no DOI recorded"
  parapraxisHistoricalRole
  "Provides historical provenance for treating slips, substitutions and forgetting as potentially structured rather than pure noise."
  "A slip is not treated as proof of a hidden wish, deliberate comparison, stable projection or recovered memory."

freudDreamSource : SourceRecord
freudDreamSource = sourceRecord
  "Sigmund Freud"
  "The Interpretation of Dreams"
  "Franz Deuticke"
  1900
  noDoiRecorded
  "no DOI recorded"
  symbolicTransformRole
  "Provides historical provenance for latent/manifest transformation and associative interpretation."
  "No universal symbol dictionary or independent verification of personal unconscious content is imported."

leveltLexicalAccessSource : SourceRecord
leveltLexicalAccessSource = sourceRecord
  "Willem J. M. Levelt; Ardi Roelofs; Antje S. Meyer"
  "A theory of lexical access in speech production"
  "Behavioral and Brain Sciences"
  1999
  doiIdentifier
  "10.1017/S0140525X99001776"
  lexicalAccessRole
  "Supports staged conceptual, lemma and phonological access with monitoring and correction."
  "The theory does not establish the personal meaning of any individual speech error."

harleyMacAndrewSource : SourceRecord
harleyMacAndrewSource = sourceRecord
  "Trevor A. Harley; Siobhan B. G. MacAndrew"
  "Constraints Upon Word Substitution Speech Errors"
  "Journal of Psycholinguistic Research"
  2001
  doiIdentifier
  "10.1023/A:1010421724343"
  speechErrorRole
  "Supports semantic, associative, shared-feature and phonological constraints on naturally occurring word substitutions."
  "A family-name intrusion is not automatically assigned a unique semantic or psychodynamic cause."

harseyFreydSource : SourceRecord
harseyFreydSource = sourceRecord
  "Sarah J. Harsey; Jennifer J. Freyd"
  "The Influence of Deny, Attack, Reverse Victim and Offender and Insincere Apologies on Perceptions of Sexual Assault"
  "Journal of Interpersonal Violence"
  2023
  doiIdentifier
  "10.1177/08862605231169751"
  darvoResearchRole
  "Supports the possibility that denial, attack and role reversal can alter observers' responsibility and credibility judgments."
  "The result is not generalized into a diagnosis or proof that every defensive family dispute is deliberate DARVO."

dutaSheafHypergraphSource : SourceRecord
dutaSheafHypergraphSource = sourceRecord
  "Iulia Duta; Giulia Cassara; Fabrizio Silvestri; Pietro Lio"
  "Sheaf Hypergraph Networks"
  "arXiv"
  2023
  doiIdentifier
  "10.48550/arXiv.2309.17116"
  typedHyperfabricRole
  "Supports a typed stalk, incidence and restriction-map carrier for higher-arity local-to-global relations."
  "No learning benchmark, neural identity claim or clinical inference is imported."

canonicalRelationalSources : List SourceRecord
canonicalRelationalSources =
  freudPsychopathologySource
  ∷ freudDreamSource
  ∷ leveltLexicalAccessSource
  ∷ harleyMacAndrewSource
  ∷ harseyFreydSource
  ∷ dutaSheafHypergraphSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalRelationalSourceCount : Nat
canonicalRelationalSourceCount = listCount canonicalRelationalSources

canonicalRelationalSourceCountIsSix :
  canonicalRelationalSourceCount ≡ 6
canonicalRelationalSourceCountIsSix = refl
