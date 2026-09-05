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

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

iterate : {A : Set} → (A → A) → Nat → A → A
iterate step zero x = x
iterate step (suc n) x = iterate step n (step x)

record ForwardTranslationData : Set₁ where
  field
    State : Set
    a b pred : State → State
    periodMinusOne : Nat
    periodReturn :
      (x : State) → a (iterate a periodMinusOne x) ≡ x
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
    (cong (pred data) (periodReturn data x))

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

repeatARuns :
  (data : ForwardTranslationData) →
  (n : Nat) →
  (tail : ForwardWord data) →
  (x : State data) →
  run data (repeatA data n tail) x
  ≡ run data tail (iterate (a data) n x)
repeatARuns data zero tail x = refl
repeatARuns data (suc n) tail x =
  repeatARuns data n tail (a data x)

predBlockWord : (data : ForwardTranslationData) → ForwardWord data
predBlockWord data = repeatA data (periodMinusOne data) (useB done)

predBlockRuns :
  (data : ForwardTranslationData) →
  (x : State data) →
  run data (predBlockWord data) x ≡ pred data x
predBlockRuns data x =
  trans
    (repeatARuns data (periodMinusOne data) (useB done) x)
    (forwardBlockIsPred data x)

_++w_ :
  {data : ForwardTranslationData} →
  ForwardWord data → ForwardWord data → ForwardWord data
done ++w right = right
(useA left) ++w right = useA (left ++w right)
(useB left) ++w right = useB (left ++w right)

runConcat :
  (data : ForwardTranslationData) →
  (left right : ForwardWord data) →
  (x : State data) →
  run data (left ++w right) x
  ≡ run data right (run data left x)
runConcat data done right x = refl
runConcat data (useA left) right x =
  runConcat data left right (a data x)
runConcat data (useB left) right x =
  runConcat data left right (b data x)

repeatWord :
  {data : ForwardTranslationData} →
  ForwardWord data → Nat → ForwardWord data
repeatWord word zero = done
repeatWord word (suc n) = word ++w repeatWord word n

repeatPredBlockRuns :
  (data : ForwardTranslationData) →
  (steps : Nat) →
  (x : State data) →
  run data (repeatWord (predBlockWord data) steps) x
  ≡ iterate (pred data) steps x
repeatPredBlockRuns data zero x = refl
repeatPredBlockRuns data (suc steps) x =
  trans
    (runConcat data
      (predBlockWord data)
      (repeatWord (predBlockWord data) steps)
      x)
    (trans
      (repeatPredBlockRuns data steps
        (run data (predBlockWord data) x))
      (cong
        (iterate (pred data) steps)
        (predBlockRuns data x)))

record DirectedForwardReachability (data : ForwardTranslationData) : Set where
  field
    reaches :
      (x y : State data) →
      Σ (ForwardWord data) (λ word → run data word x ≡ y)

open DirectedForwardReachability public

compileReach :
  (data : ForwardTranslationData) →
  CyclicPredecessorTransitive data →
  (x y : State data) →
  Σ (ForwardWord data) (λ word → run data word x ≡ y)
compileReach data cyclic x y with predReach cyclic x y
... | steps , target =
  repeatWord (predBlockWord data) steps ,
  trans (repeatPredBlockRuns data steps x) target

directedReachabilityFromCyclicPred :
  (data : ForwardTranslationData) →
  CyclicPredecessorTransitive data →
  DirectedForwardReachability data
directedReachabilityFromCyclicPred data cyclic = record
  { reaches = compileReach data cyclic }

------------------------------------------------------------------------
-- The only source-specific remainder is the standard cyclicity of predecessor
-- on ZMod (2^n).  Once supplied, the forward-translation compiler constructs
-- actual forward words witnessing directed transitivity.
------------------------------------------------------------------------

record IrreducibilityCompilerCutset : Set where
  constructor irreducibilityCompilerCutset
  field
    sourceThreeFullPeriodOwned : Bool
    affineBranchFactorizationOwned : Bool
    cyclicPredecessorAdapterOwned : Bool
    forwardTranslationBlockCompiled : Bool
    genericDirectedReachabilityCompilerOwned : Bool
    directedIrreducibilityClosed : Bool

canonicalIrreducibilityCompilerCutset : IrreducibilityCompilerCutset
canonicalIrreducibilityCompilerCutset =
  irreducibilityCompilerCutset true true false true true false

forwardTranslationCoreClosed :
  IrreducibilityCompilerCutset.forwardTranslationBlockCompiled
    canonicalIrreducibilityCompilerCutset
  ≡ true
forwardTranslationCoreClosed = refl

genericForwardReachabilityCompilerClosed :
  IrreducibilityCompilerCutset.genericDirectedReachabilityCompilerOwned
    canonicalIrreducibilityCompilerCutset
  ≡ true
genericForwardReachabilityCompilerClosed = refl

cyclicAdapterIsOnlyRemainingLeaf :
  IrreducibilityCompilerCutset.cyclicPredecessorAdapterOwned
    canonicalIrreducibilityCompilerCutset
  ≡ false
cyclicAdapterIsOnlyRemainingLeaf = refl
