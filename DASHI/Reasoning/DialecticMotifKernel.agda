module DASHI.Reasoning.DialecticMotifKernel where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

import DASHI.Algebra.Trit as T

------------------------------------------------------------------------
-- Atoms: ternary value, three lenses, three temporal gates
------------------------------------------------------------------------

data Lens : Set where
  self norm mirror : Lens

data Time : Set where
  past now future : Time

record State9 : Set where
  constructor state9
  field
    self-past self-now self-future : T.Trit
    norm-past norm-now norm-future : T.Trit
    mirror-past mirror-now mirror-future : T.Trit

open State9 public

at : State9 → Lens → Time → T.Trit
at s self past = self-past s
at s self now = self-now s
at s self future = self-future s
at s norm past = norm-past s
at s norm now = norm-now s
at s norm future = norm-future s
at s mirror past = mirror-past s
at s mirror now = mirror-now s
at s mirror future = mirror-future s

zeroState : State9
zeroState = state9 T.zer T.zer T.zer T.zer T.zer T.zer T.zer T.zer T.zer

------------------------------------------------------------------------
-- Involution and its first-principles lemma
------------------------------------------------------------------------

ι : State9 → State9
ι s =
  state9
    (T.inv (self-past s))
    (T.inv (self-now s))
    (T.inv (self-future s))
    (T.inv (norm-past s))
    (T.inv (norm-now s))
    (T.inv (norm-future s))
    (T.inv (mirror-past s))
    (T.inv (mirror-now s))
    (T.inv (mirror-future s))

ι²-id : ∀ s → ι (ι s) ≡ s
ι²-id (state9 T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg) = refl
ι²-id (state9 T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.zer) = refl
ι²-id (state9 T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.pos) = refl
ι²-id (state9 a b c d e f g h i)
  rewrite T.inv-invol a
        | T.inv-invol b
        | T.inv-invol c
        | T.inv-invol d
        | T.inv-invol e
        | T.inv-invol f
        | T.inv-invol g
        | T.inv-invol h
        | T.inv-invol i = refl

------------------------------------------------------------------------
-- Decidable atomic relations and finite counts
------------------------------------------------------------------------

tritEq : T.Trit → T.Trit → Bool
tritEq T.neg T.neg = true
tritEq T.neg T.zer = false
tritEq T.neg T.pos = false
tritEq T.zer T.neg = false
tritEq T.zer T.zer = true
tritEq T.zer T.pos = false
tritEq T.pos T.neg = false
tritEq T.pos T.zer = false
tritEq T.pos T.pos = true

not : Bool → Bool
not true = false
not false = true

_&&_ : Bool → Bool → Bool
true && b = b
false && b = false

flip : T.Trit → T.Trit → Nat
flip a b with tritEq a b
... | true = zero
... | false = suc zero

isPos : T.Trit → Nat
isPos T.pos = suc zero
isPos _ = zero

isNeg : T.Trit → Nat
isNeg T.neg = suc zero
isNeg _ = zero

isZero : T.Trit → Nat
isZero T.zer = suc zero
isZero _ = zero

fold9 : (T.Trit → Nat) → State9 → Nat
fold9 f s =
  f (self-past s) + f (self-now s) + f (self-future s) +
  f (norm-past s) + f (norm-now s) + f (norm-future s) +
  f (mirror-past s) + f (mirror-now s) + f (mirror-future s)

positiveMass negativeMass neutralLoad : State9 → Nat
positiveMass = fold9 isPos
negativeMass = fold9 isNeg
neutralLoad = fold9 isZero

tensionMass : State9 → Nat
tensionMass s = positiveMass s * negativeMass s

σ-lens : State9 → Lens → Nat
σ-lens s ℓ = flip (at s ℓ past) (at s ℓ now) + flip (at s ℓ now) (at s ℓ future)

σ : State9 → Nat
σ s = σ-lens s self + σ-lens s norm + σ-lens s mirror

-- Mirror agreement is the explicit thesis/antithesis involution relation:
-- mirror(t) should equal inv(self(t)).
mirrorMismatch : State9 → Time → Nat
mirrorMismatch s t with tritEq (at s mirror t) (T.inv (at s self t))
... | true = zero
... | false = suc zero

Δm : State9 → Nat
Δm s = mirrorMismatch s past + mirrorMismatch s now + mirrorMismatch s future

record Backbone : Set where
  constructor backbone
  field
    self₀ norm₀ mirror₀ : T.Trit

presentBackbone : State9 → Backbone
presentBackbone s = backbone (self-now s) (norm-now s) (mirror-now s)

record Invariants : Set where
  constructor invariants
  field
    backbone₀ : Backbone
    temporalInstability : Nat
    mirrorAsymmetry : Nat
    tension : Nat
    neutral : Nat
    positive : Nat
    negative : Nat

extract : State9 → Invariants
extract s =
  invariants
    (presentBackbone s)
    (σ s)
    (Δm s)
    (tensionMass s)
    (neutralLoad s)
    (positiveMass s)
    (negativeMass s)

------------------------------------------------------------------------
-- Kernels, composition, and involution compatibility
------------------------------------------------------------------------

record Kernel : Set where
  constructor kernel
  field
    run : State9 → State9
    commutes-ι : ∀ s → run (ι s) ≡ ι (run s)

open Kernel public

idKernel : Kernel
idKernel = kernel (λ s → s) (λ s → refl)

zeroKernel : Kernel
zeroKernel = kernel (λ _ → zeroState) (λ _ → refl)

_∘K_ : Kernel → Kernel → Kernel
K₂ ∘K K₁ =
  kernel
    (λ s → run K₂ (run K₁ s))
    proof
  where
    proof : ∀ s → run K₂ (run K₁ (ι s)) ≡ ι (run K₂ (run K₁ s))
    proof s rewrite commutes-ι K₁ s | commutes-ι K₂ (run K₁ s) = refl

zeroKernel-fixed : run zeroKernel zeroState ≡ zeroState
zeroKernel-fixed = refl

------------------------------------------------------------------------
-- Lens/projection relations
------------------------------------------------------------------------

record Projection (A : Set) : Set where
  constructor projection
  field observe : State9 → A

open Projection public

record ProjectionInvariant {A : Set} (P : Projection A) (K : Kernel) : Set where
  constructor projectionInvariant
  field preserved : ∀ s → observe P (run K s) ≡ observe P s

presentProjection : Projection Backbone
presentProjection = projection presentBackbone

idPresentInvariant : ProjectionInvariant presentProjection idKernel
idPresentInvariant = projectionInvariant (λ _ → refl)

------------------------------------------------------------------------
-- Motifs and deterministic policy interpretation
------------------------------------------------------------------------

data Motif : Set where
  M1 M2 M3 M4 M5 M6 M7 M8 M9 M10 : Motif

data Policy : Set where
  allow timingFence roleFence redesign buffer timeControl programOnly prohibit lift : Policy

policy : Motif → Policy
policy M1 = allow
policy M2 = timingFence
policy M3 = roleFence
policy M4 = redesign
policy M5 = buffer
policy M6 = redesign
policy M7 = timeControl
policy M8 = programOnly
policy M9 = prohibit
policy M10 = lift

atLeast3 : Nat → Bool
atLeast3 zero = false
atLeast3 (suc zero) = false
atLeast3 (suc (suc zero)) = false
atLeast3 (suc (suc (suc n))) = true

over9 : Nat → Bool
over9 zero = false
over9 (suc zero) = false
over9 (suc (suc zero)) = false
over9 (suc (suc (suc zero))) = false
over9 (suc (suc (suc (suc zero)))) = false
over9 (suc (suc (suc (suc (suc zero))))) = false
over9 (suc (suc (suc (suc (suc (suc zero)))))) = false
over9 (suc (suc (suc (suc (suc (suc (suc zero))))))) = false
over9 (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))) = false
over9 (suc (suc (suc (suc (suc (suc (suc (suc (suc zero))))))))) = false
over9 (suc (suc (suc (suc (suc (suc (suc (suc (suc (suc n)))))))))) = true

sparsePositive : Nat → Bool
sparsePositive zero = true
sparsePositive (suc zero) = true
sparsePositive _ = false

atLeast5 : Nat → Bool
atLeast5 zero = false
atLeast5 (suc zero) = false
atLeast5 (suc (suc zero)) = false
atLeast5 (suc (suc (suc zero))) = false
atLeast5 (suc (suc (suc (suc zero)))) = false
atLeast5 (suc (suc (suc (suc (suc n))))) = true

classifyCore : State9 → Motif
classifyCore s with presentBackbone s
... | backbone T.neg T.neg T.neg = M9
... | backbone T.pos T.pos T.pos with at s mirror future
...   | T.neg = M2
...   | _ with atLeast3 (σ s)
...     | true = M7
...     | false = M1
... | backbone T.pos T.neg T.pos = M3
... | backbone T.pos T.pos T.neg = M5
... | backbone T.neg T.pos T.pos = M4
... | backbone T.zer T.pos T.pos = M4
... | backbone T.neg T.zer T.pos = M4
... | backbone T.zer T.zer T.pos = M4
... | backbone T.neg T.pos T.zer = M4
... | backbone T.zer T.pos T.zer = M4
... | backbone a b c with atLeast3 (σ s)
...   | true = M7
...   | false with sparsePositive (positiveMass s) && atLeast5 (negativeMass s)
...     | true = M8
...     | false with at s mirror past
...       | T.pos = M6
...       | _ with at s mirror future
...         | T.pos = M6
...         | _ = M5

-- M10 is a containing-voxel transition, evaluated before local motif selection.
classify : State9 → Motif
classify s with over9 (neutralLoad s + tensionMass s)
... | true = M10
... | false = classifyCore s

result : State9 → Policy
result s = policy (classify s)

------------------------------------------------------------------------
-- Closed examples / executable reduction receipts
------------------------------------------------------------------------

allGreen : State9
allGreen = state9 T.pos T.pos T.pos T.pos T.pos T.pos T.pos T.pos T.pos

allRed : State9
allRed = state9 T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg T.neg

roleSplit : State9
roleSplit = state9 T.pos T.pos T.pos T.neg T.neg T.neg T.pos T.pos T.pos

mirrorSplit : State9
mirrorSplit = state9 T.pos T.pos T.pos T.pos T.pos T.pos T.neg T.neg T.neg

allGreen-classifies : classify allGreen ≡ M10
allGreen-classifies = refl

-- The current overflow rule deliberately treats high mixed/tension loads as a lift.
allRed-classifies : classify allRed ≡ M9
allRed-classifies = refl

roleSplit-classifies : classify roleSplit ≡ M10
roleSplit-classifies = refl

mirrorSplit-classifies : classify mirrorSplit ≡ M10
mirrorSplit-classifies = refl

zero-classifies : classify zeroState ≡ M5
zero-classifies = refl
