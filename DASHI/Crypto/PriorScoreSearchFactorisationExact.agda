module DASHI.Crypto.PriorScoreSearchFactorisationExact where

------------------------------------------------------------------------
-- PRIOR FACTORISATION != SCORE FACTORISATION != SEARCH FACTORISATION
--
-- This is the exact boundary identified by the MLWE/NTT blue-team analysis.
-- A prior may factor without yielding a search algorithm; a score may decompose
-- while compatibility remains global; and a search factorisation additionally
-- needs constructive local enumeration plus reconciliation/assembly.
--
-- Motivation / source boundary:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- Oded Regev, "On lattices, learning with errors, random linear codes, and
-- cryptography", STOC 2005. DOI: 10.1145/1060590.1060603.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record PriorFactorisation : Set₁ where
  constructor priorFactorisation
  field
    Hidden Left Right : Set
    left : Hidden → Left
    right : Hidden → Right
    Prior : Hidden → Set
    PriorL : Left → Set
    PriorR : Right → Set
    Coupling : Left → Right → Set
    priorDecomposes : ∀ hidden →
      Prior hidden →
      PriorL (left hidden) ×
      (PriorR (right hidden) × Coupling (left hidden) (right hidden))
open PriorFactorisation public

record ScoreFactorisation : Set₁ where
  constructor scoreFactorisation
  field
    Hidden Left Right : Set
    left : Hidden → Left
    right : Hidden → Right
    localScoreL : Left → Nat
    localScoreR : Right → Nat
    couplingScore : Left → Right → Nat
    globalScore : Hidden → Nat
    scoreDecomposes : ∀ hidden →
      globalScore hidden ≡
      localScoreL (left hidden) +
      (localScoreR (right hidden) + couplingScore (left hidden) (right hidden))
open ScoreFactorisation public

record SearchFactorisation : Set₁ where
  constructor searchFactorisation
  field
    Hidden Public LeftWitness RightWitness : Set
    enumerateLeft : Public → LeftWitness
    enumerateRight : Public → RightWitness
    Compatible : LeftWitness → RightWitness → Set
    compatible : ∀ public → Compatible (enumerateLeft public) (enumerateRight public)
    assemble : LeftWitness → RightWitness → Hidden
open SearchFactorisation public

------------------------------------------------------------------------
-- Concrete finite separation: local prior and local score are trivial, but the
-- crossed pair is globally forbidden by reconciliation.  Thus local
-- factorisation does not erase the reconciliation seam.
------------------------------------------------------------------------

data EqualBits : Bool → Bool → Set where
  equalFalse : EqualBits false false
  equalTrue : EqualBits true true

record BitPair : Set where
  constructor bitPair
  field bitL bitR : Bool
open BitPair public

bitPrior : BitPair → Set
bitPrior pair = EqualBits (bitL pair) (bitR pair)

Always : Bool → Set
Always b = b ≡ b

bitPriorFactorsLocally : ∀ pair →
  bitPrior pair →
  Always (bitL pair) × (Always (bitR pair) × EqualBits (bitL pair) (bitR pair))
bitPriorFactorsLocally pair prior = refl , (refl , prior)

bitPriorFactorisation : PriorFactorisation
bitPriorFactorisation =
  priorFactorisation BitPair Bool Bool bitL bitR bitPrior Always Always EqualBits
    bitPriorFactorsLocally

zero : Bool → Nat
zero b = 0

couplingPenalty : Bool → Bool → Nat
couplingPenalty false false = 0
couplingPenalty false true = 1
couplingPenalty true false = 1
couplingPenalty true true = 0

bitGlobalScore : BitPair → Nat
bitGlobalScore pair = couplingPenalty (bitL pair) (bitR pair)

bitScoreFactorisation : ScoreFactorisation
bitScoreFactorisation =
  scoreFactorisation BitPair Bool Bool bitL bitR zero zero couplingPenalty bitGlobalScore proof
  where
  proof : ∀ pair →
    bitGlobalScore pair ≡
    zero (bitL pair) + (zero (bitR pair) + couplingPenalty (bitL pair) (bitR pair))
  proof (bitPair false false) = refl
  proof (bitPair false true) = refl
  proof (bitPair true false) = refl
  proof (bitPair true true) = refl

crossedLocalsPassIndividually : Always false × Always true
crossedLocalsPassIndividually = refl , refl

crossedLocalsCannotReconcile : EqualBits false true → ⊥
crossedLocalsCannotReconcile ()

------------------------------------------------------------------------
-- Claim boundary.
------------------------------------------------------------------------

record FactorisationBoundary : Set where
  constructor factorisationBoundary
  field
    priorFactorisationImpliesCheapSearch : Bool
    priorFactorisationImpliesCheapSearchIsFalse :
      priorFactorisationImpliesCheapSearch ≡ false
    scoreFactorisationImpliesCheapSearch : Bool
    scoreFactorisationImpliesCheapSearchIsFalse :
      scoreFactorisationImpliesCheapSearch ≡ false
    localTestsRemoveReconciliation : Bool
    localTestsRemoveReconciliationIsFalse :
      localTestsRemoveReconciliation ≡ false

open FactorisationBoundary public

canonicalFactorisationBoundary : FactorisationBoundary
canonicalFactorisationBoundary =
  factorisationBoundary false refl false refl false refl
