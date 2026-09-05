module DASHI.Analysis.NonArchimedeanForwardTranslationIrreducibilityCompilerExact where

------------------------------------------------------------------------
-- FORWARD TRANSLATION / DIRECTED IRREDUCIBILITY COMPILER
--
-- Let a(x)=3x and b(x)=3x-1 on Z/2^nZ.  The checked source theorem
--
--   3^(2^(n-2)) = 1  (n >= 3)
--
-- implies that with L=2^(n-2), one forward block
--
--   a^(L-1) ; b
--
-- acts exactly as translation x -> x-1.  Since repeated predecessor
-- translation is transitive on the cyclic residue carrier, every state reaches
-- every other state by forward a/b steps.  This is the correct directed
-- irreducibility route; undirected Schreier connectivity is not required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (trans)

iterate : {A : Set} → (A → A) → Nat → A → A
iterate step zero x = x
iterate step (suc n) x = step (iterate step n x)

record ForwardTranslationData : Set₁ where
  field
    State : Set
    a b pred : State → State
    periodMinusOne : Nat

    -- a(a^(L-1)x)=x, i.e. the supplied source full-period theorem.
    periodReturn :
      (x : State) → a (iterate a periodMinusOne x) ≡ x

    -- b(y)=pred(a(y)); for Collatz this is 3y-1.
    bFactorsAsPredAfterA :
      (y : State) → b y ≡ pred (a y)

open ForwardTranslationData public

forwardBlock : (data : ForwardTranslationData) → State data → State data
forwardBlock data x =
  b data (iterate (a data) (periodMinusOne data) x)

forwardBlockIsPred :
  (data : ForwardTranslationData) →
  (x : State data) →
  forwardBlock data x ≡ pred data x
forwardBlockIsPred data x =
  trans
    (bFactorsAsPredAfterA data
      (iterate (a data) (periodMinusOne data) x))
    (congPred (periodReturn data x))
  where
  congPred :
    ∀ {u v} → u ≡ v → pred data u ≡ pred data v
  congPred refl = refl

record CyclicPredecessorTransitive (data : ForwardTranslationData) : Set where
  field
    predReach :
      (x y : State data) →
      Σ Nat (λ steps → iterate (pred data) steps x ≡ y)

open CyclicPredecessorTransitive public

------------------------------------------------------------------------
-- Reachability language over forward generators.
------------------------------------------------------------------------

data ForwardWord (data : ForwardTranslationData) : Set where
  done : ForwardWord data
  useA : ForwardWord data → ForwardWord data
  useB : ForwardWord data → ForwardWord data

run :
  (data : ForwardTranslationData) →
  ForwardWord data →
  State data →
  State data
run data done x = x
run data (useA word) x = run data word (a data x)
run data (useB word) x = run data word (b data x)

repeatA :
  (data : ForwardTranslationData) →
  Nat → ForwardWord data → ForwardWord data
repeatA data zero tail = tail
repeatA data (suc n) tail = useA (repeatA data n tail)

predBlockWord : (data : ForwardTranslationData) → ForwardWord data
predBlockWord data = repeatA data (periodMinusOne data) (useB done)

-- Word concatenation, executing the left word first and then the right word.
_++w_ :
  {data : ForwardTranslationData} →
  ForwardWord data → ForwardWord data → ForwardWord data
done ++w right = right
(useA left) ++w right = useA (left ++w right)
(useB left) ++w right = useB (left ++w right)

repeatWord :
  {data : ForwardTranslationData} →
  ForwardWord data → Nat → ForwardWord data
repeatWord word zero = done
repeatWord word (suc n) = word ++w repeatWord word n

record DirectedForwardReachability (data : ForwardTranslationData) : Set where
  field
    reaches :
      (x y : State data) →
      Σ (ForwardWord data) (λ word → run data word x ≡ y)

------------------------------------------------------------------------
-- The only source-specific remainder is the standard cyclicity of predecessor
-- on ZMod (2^n).  Once supplied, the forward-translation block gives the
-- directed semigroup transitivity target.
--
-- We keep this receipt explicit rather than pretending undirected graph
-- connectivity proves directed reachability.
------------------------------------------------------------------------

record IrreducibilityCompilerCutset : Set where
  constructor irreducibilityCompilerCutset
  field
    sourceThreeFullPeriodOwned : Agda.Builtin.Bool.Bool
    affineBranchFactorizationOwned : Agda.Builtin.Bool.Bool
    cyclicPredecessorAdapterOwned : Agda.Builtin.Bool.Bool
    forwardTranslationBlockCompiled : Agda.Builtin.Bool.Bool
    directedIrreducibilityClosed : Agda.Builtin.Bool.Bool

open import Agda.Builtin.Bool using (Bool; true; false)

canonicalIrreducibilityCompilerCutset : IrreducibilityCompilerCutset
canonicalIrreducibilityCompilerCutset =
  irreducibilityCompilerCutset true true false true false

forwardTranslationCoreClosed :
  IrreducibilityCompilerCutset.forwardTranslationBlockCompiled
    canonicalIrreducibilityCompilerCutset
  ≡ true
forwardTranslationCoreClosed = refl

cyclicAdapterIsOnlyRemainingLeaf :
  IrreducibilityCompilerCutset.cyclicPredecessorAdapterOwned
    canonicalIrreducibilityCompilerCutset
  ≡ false
cyclicAdapterIsOnlyRemainingLeaf = refl
