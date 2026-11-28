module DASHI.Cognition.PNF.X369ConstructiveConsumerSplitExact where

-- Original Leech-LILA: Anatolii Kornienko. DASHI extension.
-- Source-independent product construction; native arithmetic admission separate.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Sigma using (Σ; _,_; fst; snd)
open import Data.Empty using (⊥)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module Split {Input Semantic Residual Output : Set}
  (A : Input → Semantic → Semantic)
  (T : Input → Residual → Residual)
  (C : Semantic → Output) where

  State : Set
  State = Σ Semantic (λ _ → Residual)

  step : Input → State → State
  step u (z , r) = A u z , T u r

  observe : Input → State → Output
  observe u h = C (A u (fst h))

  semanticTransitionStable : (u : Input) (x y : State) →
    fst x ≡ fst y → fst (step u x) ≡ fst (step u y)
  semanticTransitionStable u (x , r) (y , s) same =
    Future.cong (A u) same

  semanticObservationStable : (u : Input) (x y : State) →
    fst x ≡ fst y → observe u x ≡ observe u y
  semanticObservationStable u x y same =
    Future.cong (λ z → C (A u z)) same

  semanticFuture : (x y : State) → fst x ≡ fst y →
    Future.TraceEquivalent step observe x y
  semanticFuture x y same inputs =
    Future.inputIndexedTraceDescent step observe fst
      semanticObservationStable semanticTransitionStable inputs x y same

-- Total latch for an alphabet with two initial tokens and arbitrary suffixes.
-- Unlike the restricted Python benchmark, other initial tokens are ignored.
data Literal : Set where
  a b j n : Literal

data Latch : Set where
  unset firstA firstB : Latch

latch : Literal → Latch → Latch
latch a unset = firstA
latch b unset = firstB
latch j unset = unset
latch n unset = unset
latch u firstA = firstA
latch u firstB = firstB

runLatch : List Literal → Latch → Latch
runLatch [] r = r
runLatch (u ∷ us) r = runLatch us (latch u r)

retainA : (us : List Literal) → runLatch us firstA ≡ firstA
retainA [] = refl
retainA (u ∷ us) = retainA us

retainB : (us : List Literal) → runLatch us firstB ≡ firstB
retainB [] = refl
retainB (u ∷ us) = retainB us

abPrefix : (us : List Literal) →
  runLatch (a ∷ b ∷ us) unset ≡ firstA
abPrefix us = retainA us

baPrefix : (us : List Literal) →
  runLatch (b ∷ a ∷ us) unset ≡ firstB
baPrefix us = retainB us

distinct : firstA ≡ firstB → ⊥
distinct ()

-- Any sufficient code for this observation must distinguish the two
-- initialized latch states, independent of the semantic coordinate.
module Memory {Semantic : Set} where
  State : Set
  State = Σ Semantic (λ _ → Latch)

  observeMemory : Literal → State → Latch
  observeMemory u h = snd h

  stepMemory : Literal → State → State
  stepMemory u (z , r) = z , latch u r

  sameSemantic : (z : Semantic) →
    fst (z , firstA) ≡ fst (z , firstB)
  sameSemantic z = refl

  memorySeparates : (z : Semantic) →
    Future.TraceEquivalent stepMemory observeMemory
      (z , firstA) (z , firstB) → ⊥
  memorySeparates z eq = distinct (Future.consHead (eq (j ∷ [])))

  semanticOnlyImpossible : (z : Semantic) →
    ((x y : State) → fst x ≡ fst y →
      Future.TraceEquivalent stepMemory observeMemory x y) → ⊥
  semanticOnlyImpossible z sound =
    memorySeparates z (sound (z , firstA) (z , firstB) refl)
