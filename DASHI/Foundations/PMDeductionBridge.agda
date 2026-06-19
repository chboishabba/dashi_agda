module DASHI.Foundations.PMDeductionBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import DASHI.Core.Prelude using (_×_; _,_; proj₁; proj₂; _⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- PM *1-*5 deduction/proposition comparison surface.
--
-- Checked laws below are ordinary Agda/stdlib substrate facts.  The module
-- does not assert that PM's proposition corpus or notation is formalized.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

Implication : Set → Set → Set
Implication A B =
  A → B

Disjunction : Set → Set → Set
Disjunction A B =
  A ⊎ B

Conjunction : Set → Set → Set
Conjunction A B =
  A × B

Equivalence : Set → Set → Set
Equivalence A B =
  (A → B) × (B → A)

identityImplication :
  ∀ {A : Set} →
  Implication A A
identityImplication x =
  x

conjunctionElimLeft :
  ∀ {A B : Set} →
  Conjunction A B →
  A
conjunctionElimLeft =
  proj₁

conjunctionElimRight :
  ∀ {A B : Set} →
  Conjunction A B →
  B
conjunctionElimRight =
  proj₂

conjunctionIntro :
  ∀ {A B : Set} →
  A →
  B →
  Conjunction A B
conjunctionIntro a b =
  a , b

disjunctionIntroLeft :
  ∀ {A B : Set} →
  A →
  Disjunction A B
disjunctionIntroLeft =
  inj₁

disjunctionIntroRight :
  ∀ {A B : Set} →
  B →
  Disjunction A B
disjunctionIntroRight =
  inj₂

equivalenceRefl :
  ∀ {A : Set} →
  Equivalence A A
equivalenceRefl =
  identityImplication , identityImplication

boolImplicationReflexive :
  Implication (true ≡ true) (true ≡ true)
boolImplicationReflexive =
  identityImplication

boolConjunctionRoundTrip :
  Conjunction (true ≡ true) (false ≡ false)
boolConjunctionRoundTrip =
  refl , refl

boolEquivalenceRefl :
  Equivalence (true ≡ true) (true ≡ true)
boolEquivalenceRefl =
  equivalenceRefl

data PMDeductionSurfaceKind : Set where
  star1PrimitivePropositionSurface :
    PMDeductionSurfaceKind

  star2FormalImplicationSurface :
    PMDeductionSurfaceKind

  star3LogicalProductSurface :
    PMDeductionSurfaceKind

  star4LogicalSumSurface :
    PMDeductionSurfaceKind

  star5EquivalenceSurface :
    PMDeductionSurfaceKind

canonicalPMDeductionSurfaceKinds : List PMDeductionSurfaceKind
canonicalPMDeductionSurfaceKinds =
  star1PrimitivePropositionSurface
  ∷ star2FormalImplicationSurface
  ∷ star3LogicalProductSurface
  ∷ star4LogicalSumSurface
  ∷ star5EquivalenceSurface
  ∷ []

canonicalPMDeductionSurfaceKindCount : Nat
canonicalPMDeductionSurfaceKindCount =
  listCount canonicalPMDeductionSurfaceKinds

record PMDeductionAuthorityBoundary : Set where
  constructor mkPMDeductionAuthorityBoundary
  field
    boundaryLabel :
      String

    checkedAgdaSubstratePresent :
      Bool

    checkedAgdaSubstratePresentIsTrue :
      checkedAgdaSubstratePresent ≡ true

    pmPropositionCorpusAuthority :
      Bool

    pmPropositionCorpusAuthorityIsFalse :
      pmPropositionCorpusAuthority ≡ false

    exactPMNotationAuthority :
      Bool

    exactPMNotationAuthorityIsFalse :
      exactPMNotationAuthority ≡ false

canonicalPMDeductionAuthorityBoundary :
  PMDeductionAuthorityBoundary
canonicalPMDeductionAuthorityBoundary =
  mkPMDeductionAuthorityBoundary
    "pm-deduction-bridge-boundary"
    true
    refl
    false
    refl
    false
    refl

pmDeductionBridgeDoesNotPromoteCorpus :
  PMDeductionAuthorityBoundary.pmPropositionCorpusAuthority
    canonicalPMDeductionAuthorityBoundary
  ≡
  false
pmDeductionBridgeDoesNotPromoteCorpus =
  refl
