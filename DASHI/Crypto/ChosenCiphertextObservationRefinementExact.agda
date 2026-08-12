module DASHI.Crypto.ChosenCiphertextObservationRefinementExact where

------------------------------------------------------------------------
-- ADAPTIVE OBSERVATION / CANDIDATE-FIBRE REFINEMENT
--
-- Blue-team abstraction for active protocol observations.  An observation
-- need not recover the hidden state to be security-relevant: it may merely
-- eliminate candidate hidden states.  This module proves the exact monotonic
-- refinement law and distinguishes secret-independent observations from
-- observations that split a hidden fibre.
--
-- Motivation / protocol reference:
-- Gorjan Alagic, Elaine Barker, Lily Chen, Dustin Moody, Angela Robinson,
-- Hamilton Silberg, Noah Waller,
-- "Recommendations for Key-Encapsulation Mechanisms", NIST SP 800-227,
-- 2025. DOI: 10.6028/NIST.SP.800-227.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (sym)

record ObservationSystem : Set₁ where
  constructor observationSystem
  field
    Hidden Query Observation : Set
    observe : Hidden → Query → Observation

open ObservationSystem public

record ObservationSample (system : ObservationSystem) : Set where
  constructor observationSample
  field
    query : Query system
    result : Observation system

open ObservationSample public

CompatibleWithSample :
  (system : ObservationSystem) →
  Hidden system → ObservationSample system → Set
CompatibleWithSample system candidate sample =
  observe system candidate (query sample) ≡ result sample

ConsistentWith :
  (system : ObservationSystem) →
  Hidden system → List (ObservationSample system) → Set
ConsistentWith system candidate [] = ⊤
ConsistentWith system candidate (sample ∷ rest) =
  CompatibleWithSample system candidate sample
  × ConsistentWith system candidate rest

-- Adding an observation can only narrow the candidate fibre.
refinementIsMonotone :
  ∀ {system candidate sample transcript} →
  ConsistentWith system candidate (sample ∷ transcript) →
  ConsistentWith system candidate transcript
refinementIsMonotone (_ , rest) = rest

emptyTranscriptAdmitsEveryCandidate :
  ∀ {system} (candidate : Hidden system) →
  ConsistentWith system candidate []
emptyTranscriptAdmitsEveryCandidate candidate = tt

honestSample :
  (system : ObservationSystem) →
  Hidden system → Query system → ObservationSample system
honestSample system hidden q =
  observationSample q (observe system hidden q)

honestStateSurvivesOneObservation :
  ∀ {system} (hidden : Hidden system) (q : Query system) →
  CompatibleWithSample system hidden (honestSample system hidden q)
honestStateSurvivesOneObservation hidden q = refl

------------------------------------------------------------------------
-- Secret-independent observations do not split hidden candidates.
------------------------------------------------------------------------

record SecretIndependentObservation
    (system : ObservationSystem) : Set₁ where
  constructor secretIndependentObservation
  field
    sameObservation :
      ∀ left right q →
      observe system left q ≡ observe system right q

open SecretIndependentObservation public

secretIndependentSampleCannotSeparate :
  ∀ {system}
    (independent : SecretIndependentObservation system)
    (actual candidate : Hidden system)
    (q : Query system) →
  CompatibleWithSample system candidate (honestSample system actual q)
secretIndependentSampleCannotSeparate independent actual candidate q =
  sameObservation independent candidate actual q

------------------------------------------------------------------------
-- Exact split witness: two hidden states agree at the prior public surface but
-- one query produces observably different outcomes.  No implementation timing
-- or deployed-system oracle is assumed here.
------------------------------------------------------------------------

record ObservationSplitWitness
    (system : ObservationSystem) : Set where
  constructor observationSplitWitness
  field
    left right : Hidden system
    distinguishingQuery : Query system
    outcomesDiffer :
      observe system left distinguishingQuery
      ≡ observe system right distinguishingQuery → ⊥

open ObservationSplitWitness public

rightCandidateRejectedByLeftObservation :
  ∀ {system}
    (split : ObservationSplitWitness system) →
  CompatibleWithSample system
    (right split)
    (honestSample system (left split) (distinguishingQuery split)) →
  ⊥
rightCandidateRejectedByLeftObservation split equality =
  outcomesDiffer split (sym equality)

------------------------------------------------------------------------
-- Protocol composition principle: if an externally visible protocol outcome
-- depends on hidden state, it belongs to the observation surface.  Hiding that
-- coordinate in a KEM-only model would under-model the adversary.
------------------------------------------------------------------------

record ProtocolObservationExtension
    (system : ObservationSystem) : Set₁ where
  constructor protocolObservationExtension
  field
    Outcome : Set
    outcome : Hidden system → Query system → Outcome

open ProtocolObservationExtension public

record ExtendedObservation
    {system : ObservationSystem}
    (extension : ProtocolObservationExtension system) : Set where
  constructor extendedObservation
  field
    baseObservation : Observation system
    protocolOutcome : Outcome extension

open ExtendedObservation public

extendSystem :
  ∀ {system} →
  ProtocolObservationExtension system →
  ObservationSystem
extendSystem {system} extension =
  observationSystem
    (Hidden system)
    (Query system)
    (ExtendedObservation extension)
    (λ hidden q →
      extendedObservation
        (observe system hidden q)
        (outcome extension hidden q))
