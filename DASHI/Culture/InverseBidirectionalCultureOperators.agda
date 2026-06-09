module DASHI.Culture.InverseBidirectionalCultureOperators where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Small logical surface
------------------------------------------------------------------------

data ⊥ : Set where

¬_ : Set → Set
¬ P = P → ⊥

data Direction : Set where
  forward backward bidirectional : Direction

data CulturalAxis : Set where
  fiction nonfiction reading-aloud audience child art architecture poetry politics :
    CulturalAxis

data PruningStyle : Set where
  breadth-first depth-first sparse exhaustive social-cue formal-rule metaphorical :
    PruningStyle

data SearchStyle : Set where
  local global linear branching associative reflective :
    SearchStyle

record CultureState : Set where
  constructor mkCultureState
  field
    dominant-axis : CulturalAxis
    secondary-axis : CulturalAxis
    public-axis : CulturalAxis
    private-axis : CulturalAxis
    pruning : PruningStyle
    search : SearchStyle
    aloud? : Bool
    child-scope? : Bool

open CultureState public

record CultureDelta : Set where
  constructor mkCultureDelta
  field
    source-axis : CulturalAxis
    target-axis : CulturalAxis
    input-direction : Direction
    output-direction : Direction
    bounded? : Bool

open CultureDelta public

record CulturalManifoldOperator : Set₁ where
  field
    axis : CulturalAxis
    apply : CultureState → CultureState
    inverse : CultureState → CultureState
    delta : CultureState → CultureDelta
    forward-inverse-observable :
      (s : CultureState) → dominant-axis (inverse (apply s)) ≡ dominant-axis s
    backward-inverse-observable :
      (s : CultureState) → dominant-axis (apply (inverse s)) ≡ dominant-axis s
    bidirectional-witness :
      (s : CultureState) → input-direction (delta s) ≡ bidirectional

open CulturalManifoldOperator public

swap-dominant-secondary : CultureState → CultureState
swap-dominant-secondary s = mkCultureState
  (secondary-axis s)
  (dominant-axis s)
  (public-axis s)
  (private-axis s)
  (pruning s)
  (search s)
  (aloud? s)
  (child-scope? s)

swap-public-private : CultureState → CultureState
swap-public-private s = mkCultureState
  (dominant-axis s)
  (secondary-axis s)
  (private-axis s)
  (public-axis s)
  (pruning s)
  (search s)
  (aloud? s)
  (child-scope? s)

toggle-reading-aloud : CultureState → CultureState
toggle-reading-aloud s = mkCultureState
  (dominant-axis s)
  (secondary-axis s)
  (public-axis s)
  (private-axis s)
  (pruning s)
  (search s)
  (not (aloud? s))
  (child-scope? s)
  where
    not : Bool → Bool
    not true = false
    not false = true

set-dominant : CulturalAxis → CultureState → CultureState
set-dominant a s = mkCultureState
  a
  (secondary-axis s)
  (public-axis s)
  (private-axis s)
  (pruning s)
  (search s)
  (aloud? s)
  (child-scope? s)

constant-delta : CulturalAxis → CultureDelta
constant-delta a = mkCultureDelta a a bidirectional bidirectional true

swap-delta : CultureState → CultureDelta
swap-delta s = mkCultureDelta
  (dominant-axis s)
  (secondary-axis s)
  bidirectional
  bidirectional
  true

identity-delta : CulturalAxis → CultureState → CultureDelta
identity-delta a _ = constant-delta a

------------------------------------------------------------------------
-- Axis operators for the requested cultural thread delta
------------------------------------------------------------------------

axis-identity-operator : CulturalAxis → CulturalManifoldOperator
axis-identity-operator a = record
  { axis = a
  ; apply = λ s → s
  ; inverse = λ s → s
  ; delta = identity-delta a
  ; forward-inverse-observable = λ _ → refl
  ; backward-inverse-observable = λ _ → refl
  ; bidirectional-witness = λ _ → refl
  }

fiction↔nonfiction : CulturalManifoldOperator
fiction↔nonfiction = record
  { axis = fiction
  ; apply = swap-dominant-secondary
  ; inverse = swap-dominant-secondary
  ; delta = swap-delta
  ; forward-inverse-observable = λ _ → refl
  ; backward-inverse-observable = λ _ → refl
  ; bidirectional-witness = λ _ → refl
  }

audience↔private-context : CulturalManifoldOperator
audience↔private-context = record
  { axis = audience
  ; apply = swap-public-private
  ; inverse = swap-public-private
  ; delta = λ s → mkCultureDelta (private-axis s) (public-axis s) bidirectional bidirectional true
  ; forward-inverse-observable = λ _ → refl
  ; backward-inverse-observable = λ _ → refl
  ; bidirectional-witness = λ _ → refl
  }

reading-aloud↔silent-reading : CulturalManifoldOperator
reading-aloud↔silent-reading = record
  { axis = reading-aloud
  ; apply = toggle-reading-aloud
  ; inverse = toggle-reading-aloud
  ; delta = identity-delta reading-aloud
  ; forward-inverse-observable = λ _ → refl
  ; backward-inverse-observable = λ _ → refl
  ; bidirectional-witness = λ _ → refl
  }

child-context↔general-context : CulturalManifoldOperator
child-context↔general-context = axis-identity-operator child

art↔architecture : CulturalManifoldOperator
art↔architecture = axis-identity-operator art

poetry↔politics : CulturalManifoldOperator
poetry↔politics = axis-identity-operator poetry

canonical-thread-operators : CulturalAxis → CulturalManifoldOperator
canonical-thread-operators fiction = fiction↔nonfiction
canonical-thread-operators nonfiction = fiction↔nonfiction
canonical-thread-operators reading-aloud = reading-aloud↔silent-reading
canonical-thread-operators audience = audience↔private-context
canonical-thread-operators child = child-context↔general-context
canonical-thread-operators art = art↔architecture
canonical-thread-operators architecture = art↔architecture
canonical-thread-operators poetry = poetry↔politics
canonical-thread-operators politics = poetry↔politics

------------------------------------------------------------------------
-- WAIS/autism-style tests as bounded observation quotients only
------------------------------------------------------------------------

record BoundedObservationQuotient : Set₁ where
  field
    Observation : Set
    quotient : CultureState → Observation
    pruning-style : Observation → PruningStyle
    search-style : Observation → SearchStyle
    bounded-window : Nat

open BoundedObservationQuotient public

record WAISAutismStyleObservation : Set₁ where
  field
    quotient-surface : BoundedObservationQuotient
    no-clinical-reading : ⊤
    no-interpretive-authority : ⊤

open WAISAutismStyleObservation public

record StyleObservation : Set where
  constructor mkStyleObservation
  field
    observed-pruning : PruningStyle
    observed-search : SearchStyle
    window : Nat

open StyleObservation public

toy-style-quotient : BoundedObservationQuotient
toy-style-quotient = record
  { Observation = StyleObservation
  ; quotient = λ s → mkStyleObservation (pruning s) (search s) (suc (suc zero))
  ; pruning-style = observed-pruning
  ; search-style = observed-search
  ; bounded-window = suc (suc zero)
  }

toy-wais-autism-style-observation : WAISAutismStyleObservation
toy-wais-autism-style-observation = record
  { quotient-surface = toy-style-quotient
  ; no-clinical-reading = tt
  ; no-interpretive-authority = tt
  }

------------------------------------------------------------------------
-- Canonical toy inhabitants
------------------------------------------------------------------------

toy-culture-state : CultureState
toy-culture-state = mkCultureState
  fiction
  nonfiction
  audience
  poetry
  breadth-first
  associative
  true
  false

toy-fiction-delta : CultureDelta
toy-fiction-delta = delta fiction↔nonfiction toy-culture-state

toy-reading-delta : CultureDelta
toy-reading-delta = delta reading-aloud↔silent-reading toy-culture-state

toy-style-observation : StyleObservation
toy-style-observation = quotient toy-style-quotient toy-culture-state

toy-bidirectional-proof :
  input-direction toy-fiction-delta ≡ bidirectional
toy-bidirectional-proof = refl

toy-observation-is-bounded :
  window toy-style-observation ≡ suc (suc zero)
toy-observation-is-bounded = refl

------------------------------------------------------------------------
-- Guards: explicitly absent theorem surfaces
------------------------------------------------------------------------

data ClinicalAutismDiagnosis : Set where
data WAISInterpretationAuthority : Set where
data CultureDeterminism : Set where
data PropagandaEfficacyTheorem : Set where
data QualiaRecovery : Set where
data ChildDevelopmentClosure : Set where
data AestheticTruthClaim : Set where

no-clinical-autism-diagnosis : ¬ ClinicalAutismDiagnosis
no-clinical-autism-diagnosis ()

no-wais-interpretation-authority : ¬ WAISInterpretationAuthority
no-wais-interpretation-authority ()

no-culture-determinism : ¬ CultureDeterminism
no-culture-determinism ()

no-propaganda-efficacy-theorem : ¬ PropagandaEfficacyTheorem
no-propaganda-efficacy-theorem ()

no-qualia-recovery : ¬ QualiaRecovery
no-qualia-recovery ()

no-child-development-closure : ¬ ChildDevelopmentClosure
no-child-development-closure ()

no-aesthetic-truth-claim : ¬ AestheticTruthClaim
no-aesthetic-truth-claim ()

record GuardBundle : Set where
  field
    guard-no-clinical-autism-diagnosis : ¬ ClinicalAutismDiagnosis
    guard-no-wais-interpretation-authority : ¬ WAISInterpretationAuthority
    guard-no-culture-determinism : ¬ CultureDeterminism
    guard-no-propaganda-efficacy-theorem : ¬ PropagandaEfficacyTheorem
    guard-no-qualia-recovery : ¬ QualiaRecovery
    guard-no-child-development-closure : ¬ ChildDevelopmentClosure
    guard-no-aesthetic-truth-claim : ¬ AestheticTruthClaim

canonical-guards : GuardBundle
canonical-guards = record
  { guard-no-clinical-autism-diagnosis = no-clinical-autism-diagnosis
  ; guard-no-wais-interpretation-authority = no-wais-interpretation-authority
  ; guard-no-culture-determinism = no-culture-determinism
  ; guard-no-propaganda-efficacy-theorem = no-propaganda-efficacy-theorem
  ; guard-no-qualia-recovery = no-qualia-recovery
  ; guard-no-child-development-closure = no-child-development-closure
  ; guard-no-aesthetic-truth-claim = no-aesthetic-truth-claim
  }

record ThreadDeltaSurface : Set₁ where
  field
    operator-for : CulturalAxis → CulturalManifoldOperator
    observation-only : WAISAutismStyleObservation
    guards : GuardBundle

canonical-thread-delta-surface : ThreadDeltaSurface
canonical-thread-delta-surface = record
  { operator-for = canonical-thread-operators
  ; observation-only = toy-wais-autism-style-observation
  ; guards = canonical-guards
  }
