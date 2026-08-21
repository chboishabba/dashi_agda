module DASHI.Reasoning.AristotleMCGSHypergraphExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Source
--
-- Aristotle: IMO-level Automated Theorem Proving
-- The Harmonic Team
-- arXiv:2510.01346v1 [cs.AI], 1 October 2025
-- https://arxiv.org/abs/2510.01346
--
-- This module formalises the proof-theoretic/search-structural content of
-- Sections 2.1--2.2.  It deliberately does NOT formalise empirical claims
-- about model quality, scaling, PUCT convergence, or IMO performance.
--
-- Paper architecture captured here:
--   * Lean proof states and actions;
--   * an action may produce several successor states (hyperedge);
--   * a state is solved when SOME outgoing action succeeds (OR);
--   * an action succeeds when ALL successor states are solved (AND);
--   * observational state equivalence induces fibres / graph quotienting;
--   * lemma-feedback iterations preserve already-proved lemmas.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Small dependency-free logical infrastructure.
------------------------------------------------------------------------

data All {A : Set} (P : A → Set) : List A → Set where
  all[]  : All P []
  _all∷_ : ∀ {x xs} → P x → All P xs → All P (x ∷ xs)

mapAll : ∀ {A : Set} {P Q : A → Set} {xs : List A}
       → (∀ {x} → P x → Q x)
       → All P xs
       → All Q xs
mapAll f all[] = all[]
mapAll f (px all∷ pxs) = f px all∷ mapAll f pxs

sym≡ : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym≡ refl = refl

trans≡ : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans≡ refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Search hypergraph.
--
-- The paper's "hypertree" becomes a hypergraph after identifying states
-- and actions up to the selected equivalences.  We separate the raw graph
-- from the observer/quotient layer below.
------------------------------------------------------------------------

record SearchHypergraph : Set₁ where
  field
    State   : Set
    Action  : Set

    -- An action is attempted at one source state and may split into many
    -- successor proof states.
    source  : Action → State
    targets : Action → List State

open SearchHypergraph public

------------------------------------------------------------------------
-- Exact AND/OR proof semantics.
--
-- This is the central logical statement in Section 2.1.3:
--
--   state success  = OR over outgoing successful actions
--   action success = AND over all resulting successful states
--
-- The mutual inductive definition is itself a finite proof certificate.
------------------------------------------------------------------------

mutual
  data StateProved (G : SearchHypergraph) : State G → Set where
    byAction : ∀ {s : State G} (a : Action G)
             → source G a ≡ s
             → ActionProved G a
             → StateProved G s

  data ActionProved (G : SearchHypergraph) : Action G → Set where
    allTargets : ∀ {a : Action G}
               → All (StateProved G) (targets G a)
               → ActionProved G a

-- Empty-target actions are terminal successes: they correspond to the
-- paper's empty leaves, where no Lean goals remain.
terminalActionProved : ∀ (G : SearchHypergraph) (a : Action G)
                     → targets G a ≡ []
                     → ActionProved G a
terminalActionProved G a refl = allTargets all[]

-- A one-step terminal action proves its source state.
terminalSourceProved : ∀ (G : SearchHypergraph) (a : Action G)
                     → targets G a ≡ []
                     → StateProved G (source G a)
terminalSourceProved G a h = byAction a refl (terminalActionProved G a h)

------------------------------------------------------------------------
-- Observer fibres and quotient semantics.
--
-- Aristotle identifies states when their goal expressions, local-context
-- expressions, and local-variable names agree.  Rather than hard-coding a
-- Lean syntax datatype, we expose that canonicalisation as an observer.
-- States in the same observer fibre are observationally equivalent.
------------------------------------------------------------------------

record StateObserver (G : SearchHypergraph) : Set₁ where
  field
    Observable : Set
    observe    : State G → Observable

open StateObserver public

Fibre : ∀ {G : SearchHypergraph}
      → (O : StateObserver G)
      → Observable O
      → Set
Fibre {G} O o = Σ (State G) λ s → observe O s ≡ o

_≈[_]_ : ∀ {G : SearchHypergraph}
       → State G → StateObserver G → State G → Set
x ≈[ O ] y = observe O x ≡ observe O y

observerRefl : ∀ {G : SearchHypergraph} (O : StateObserver G) (s : State G)
             → s ≈[ O ] s
observerRefl O s = refl

observerSym : ∀ {G : SearchHypergraph} {O : StateObserver G} {s t : State G}
            → s ≈[ O ] t → t ≈[ O ] s
observerSym = sym≡

observerTrans : ∀ {G : SearchHypergraph} {O : StateObserver G}
                  {r s t : State G}
              → r ≈[ O ] s → s ≈[ O ] t → r ≈[ O ] t
observerTrans = trans≡

-- Membership in one observer fibre implies observational equivalence.
sameFibre⇒equivalent : ∀ {G : SearchHypergraph} {O : StateObserver G}
                         {o : Observable O}
                       → (x y : Fibre O o)
                       → fst x ≈[ O ] fst y
sameFibre⇒equivalent (x , hx) (y , hy) = trans≡ hx (sym≡ hy)

------------------------------------------------------------------------
-- Quotient-sound proof reuse.
--
-- The paper notes that state equivalence is operationally useful but is
-- not perfectly extensional for every tactic (aesop can inspect global
-- state).  Therefore proof transport across an observer fibre is NOT made
-- automatic here: it is explicit evidence/a contract.
------------------------------------------------------------------------

record QuotientSound (G : SearchHypergraph) (O : StateObserver G) : Set where
  field
    transportProof : ∀ {s t : State G}
                   → s ≈[ O ] t
                   → StateProved G s
                   → StateProved G t

open QuotientSound public

-- Under an explicit quotient-soundness witness, every two points of a
-- fibre share provability.
fibreProofTransport : ∀ {G : SearchHypergraph} {O : StateObserver G}
                        (Q : QuotientSound G O)
                        {o : Observable O}
                        (x y : Fibre O o)
                    → StateProved G (fst x)
                    → StateProved G (fst y)
fibreProofTransport Q x y = transportProof Q (sameFibre⇒equivalent x y)

------------------------------------------------------------------------
-- Action equivalence induced by observable transitions.
--
-- The paper treats actions as equivalent when the transitions they induce
-- are equivalent.  Pointwise equality of observed target lists is a clean,
-- stronger exact version of that idea.
------------------------------------------------------------------------

observeList : ∀ {G : SearchHypergraph}
            → (O : StateObserver G)
            → List (State G)
            → List (Observable O)
observeList O [] = []
observeList O (x ∷ xs) = observe O x ∷ observeList O xs

record ActionEquivalent {G : SearchHypergraph}
                        (O : StateObserver G)
                        (a b : Action G) : Set where
  field
    sameSource  : source G a ≈[ O ] source G b
    sameTargets : observeList O (targets G a) ≡ observeList O (targets G b)

------------------------------------------------------------------------
-- Lemma-based outer reasoning with formal feedback (Section 2.2).
------------------------------------------------------------------------

data LemmaStatus : Set where
  unknown unproved proved : LemmaStatus

record LemmaLedger : Set₁ where
  field
    LemmaId : Set
    status  : LemmaId → LemmaStatus

open LemmaLedger public

IsProved : LemmaStatus → Set
IsProved proved = ⊤
IsProved unknown = Σ ⊤ λ _ → tt ≡ tt
IsProved unproved = Σ ⊤ λ _ → tt ≡ tt

-- We need an actually discriminating proposition for preservation, so use
-- equality to the distinguished status rather than IsProved above.
ProvedIn : (L : LemmaLedger) → LemmaId L → Set
ProvedIn L l = status L l ≡ proved

record FeedbackRefinement (old new : LemmaLedger) : Set₁ where
  field
    sameLemmaId : LemmaId old ≡ LemmaId new

    -- Cast a lemma identifier across the equality of identifier spaces.
    castId : LemmaId old → LemmaId new

    -- Core Aristotle iteration invariant: revised lemma collections keep
    -- lemmas which formal search has already proved.
    preservesProved : ∀ (l : LemmaId old)
                    → ProvedIn old l
                    → ProvedIn new (castId l)

open FeedbackRefinement public

-- Composition-free local theorem exposing the monotonicity invariant.
provedKnowledgeMonotone : ∀ {old new : LemmaLedger}
                            (R : FeedbackRefinement old new)
                            (l : LemmaId old)
                        → ProvedIn old l
                        → ProvedIn new (castId R l)
provedKnowledgeMonotone R l = preservesProved R l

------------------------------------------------------------------------
-- A compact paper-level architecture record.
------------------------------------------------------------------------

record AristotleKernel : Set₁ where
  field
    graph    : SearchHypergraph
    observer : StateObserver graph

    -- Required before quotienting is allowed to transport proof evidence.
    quotientSound : QuotientSound graph observer

    -- Human-readable provenance/guard, useful when this kernel is embedded
    -- in a larger DASHI evidence loom.
    sourceReading : String

open AristotleKernel public

canonicalReading : String
canonicalReading =
  "Aristotle (Harmonic Team), arXiv:2510.01346v1: MCGS search hypergraph with OR-state / AND-action semantics and iterative lemma feedback."
