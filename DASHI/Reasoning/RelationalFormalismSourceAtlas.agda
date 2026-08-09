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
  attractorStabilityRole viabilityGeometryRole : SourceRole
  dynamicProgrammingRole interferenceHierarchyRole : SourceRole

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

lasalleAttractorSource : SourceRecord
lasalleAttractorSource = sourceRecord
  "Joseph P. LaSalle"
  "Some Extensions of Liapunov's Second Method"
  "IRE Transactions on Circuit Theory"
  1960
  doiIdentifier
  "10.1109/TCT.1960.1086720"
  attractorStabilityRole
  "Supports using a decreasing value function and a region of attraction to distinguish local activity from return toward a desired invariant set."
  "A relational goal is not asserted to be a literal autonomous differential-system attractor, and no empirical Lyapunov function is inferred from narrative data."

aubinViabilitySource : SourceRecord
aubinViabilitySource = sourceRecord
  "Jean-Pierre Aubin"
  "A Survey of Viability Theory"
  "SIAM Journal on Control and Optimization"
  1990
  doiIdentifier
  "10.1137/0328044"
  viabilityGeometryRole
  "Supports separating globally nameable states from trajectories that remain viable under state-dependent constraints and controls."
  "A nominal option is not thereby proved feasible for a particular person, and viability is not identified with moral desirability."

bellmanDynamicProgrammingSource : SourceRecord
bellmanDynamicProgrammingSource = sourceRecord
  "Richard Bellman"
  "Dynamic Programming"
  "Princeton University Press"
  1957
  doiIdentifier
  "10.1515/9781400835386"
  dynamicProgrammingRole
  "Supports state-indexed finite policy comparison and the principle that a choice must be evaluated together with its continuation value."
  "The repository does not claim a unique scalar utility for every relational value or that the finite witness portfolio solves an empirical person's life."

sorkinQuantumMeasureSource : SourceRecord
sorkinQuantumMeasureSource = sourceRecord
  "Rafael D. Sorkin"
  "Quantum Mechanics as Quantum Measure Theory"
  "Modern Physics Letters A"
  1994
  doiIdentifier
  "10.1142/S021773239400294X"
  interferenceHierarchyRole
  "Supports distinguishing diagonal, pairwise-interference and possible higher-order residual terms in multi-alternative intensity accounting."
  "The relational branch model is not promoted to literal quantum mechanics, physical collapse, a Born rule, or quantum cognition."

canonicalRelationalSources : List SourceRecord
canonicalRelationalSources =
  freudPsychopathologySource
  ∷ freudDreamSource
  ∷ leveltLexicalAccessSource
  ∷ harleyMacAndrewSource
  ∷ harseyFreydSource
  ∷ dutaSheafHypergraphSource
  ∷ lasalleAttractorSource
  ∷ aubinViabilitySource
  ∷ bellmanDynamicProgrammingSource
  ∷ sorkinQuantumMeasureSource
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = zero
listCount (_ ∷ xs) = suc (listCount xs)

canonicalRelationalSourceCount : Nat
canonicalRelationalSourceCount = listCount canonicalRelationalSources

canonicalRelationalSourceCountIsTen :
  canonicalRelationalSourceCount ≡ 10
canonicalRelationalSourceCountIsTen = refl
