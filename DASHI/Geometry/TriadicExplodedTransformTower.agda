module DASHI.Geometry.TriadicExplodedTransformTower where

-- Constructive geometry layer for the DASHI ternary/involution programme.
--
-- Proved here: ternary involution, pullback equivariance, atomic and exploded
-- transform equivariance, and typed interfaces for scale commutation and MDL.
-- Not promoted here: analytic universality, continuum convergence, or codec
-- superiority.  Those require explicit metric and empirical receipts.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Primitive using (Level; _⊔_; lsuc)

private
  variable
    ℓG ℓC ℓU : Level
    G : Set ℓG
    C : Set ℓC

------------------------------------------------------------------------
-- Primitive balanced ternary carrier and involution.

data Trit : Set where
  neg : Trit
  zeroT : Trit
  pos : Trit

ιT : Trit → Trit
ιT neg = pos
ιT zeroT = zeroT
ιT pos = neg

ιT-involutive : ∀ t → ιT (ιT t) ≡ t
ιT-involutive neg = refl
ιT-involutive zeroT = refl
ιT-involutive pos = refl

State : Set ℓG → Set ℓC → Set (ℓG ⊔ ℓC)
State G C = G → C → Trit

ιS : State G C → State G C
ιS s g c = ιT (s g c)

ιS-involutive : (s : State G C) → (g : G) → (c : C) →
  ιS (ιS s) g c ≡ s g c
ιS-involutive s g c = ιT-involutive (s g c)

------------------------------------------------------------------------
-- Geometry acts on indices by pullback and commutes with sign involution.

Warp : Set ℓG → Set ℓG
Warp G = G → G

pullback : Warp G → State G C → State G C
pullback w s g c = s (w g) c

pullback-commutes-with-involution :
  (w : Warp G) → (s : State G C) → (g : G) → (c : C) →
  ιS (pullback w s) g c ≡ pullback w (ιS s) g c
pullback-commutes-with-involution w s g c = refl

------------------------------------------------------------------------
-- Atomic and exploded transforms.

record AtomicTransform (G : Set ℓG) : Set ℓG where
  constructor atomic
  field
    support : G → Bool
    localWarp : Warp G

open AtomicTransform public

applyAtomicAt : AtomicTransform G → State G C → G → C → Trit
applyAtomicAt a s g c with support a g
... | true = s (localWarp a g) c
... | false = s g c

applyAtomic : AtomicTransform G → State G C → State G C
applyAtomic a s g c = applyAtomicAt a s g c

applyAtomic-commutes-with-involution :
  (a : AtomicTransform G) → (s : State G C) → (g : G) → (c : C) →
  ιT (applyAtomicAt a s g c) ≡ applyAtomicAt a (ιS s) g c
applyAtomic-commutes-with-involution a s g c with support a g
... | true = refl
... | false = refl

ExplodedTransform : Set ℓG → Set ℓG
ExplodedTransform G = List (AtomicTransform G)

-- Pointwise ordered application.  This avoids assuming disjoint supports;
-- a separate partition receipt records that stronger codec/tree condition.
applyExplodedAt : ExplodedTransform G → State G C → G → C → Trit
applyExplodedAt [] s g c = s g c
applyExplodedAt (a ∷ as) s g c with support a g
... | true = applyExplodedAt as s (localWarp a g) c
... | false = applyExplodedAt as s g c

applyExploded : ExplodedTransform G → State G C → State G C
applyExploded xs s g c = applyExplodedAt xs s g c

applyExploded-commutes-with-involution :
  (xs : ExplodedTransform G) → (s : State G C) → (g : G) → (c : C) →
  ιT (applyExplodedAt xs s g c) ≡ applyExplodedAt xs (ιS s) g c
applyExploded-commutes-with-involution [] s g c = refl
applyExploded-commutes-with-involution (a ∷ as) s g c with support a g
... | true = applyExploded-commutes-with-involution as s (localWarp a g) c
... | false = applyExploded-commutes-with-involution as s g c

------------------------------------------------------------------------
-- Partition-tree / recognisability receipt.

record PartitionSurface (G : Set ℓG) : Set (lsuc ℓG) where
  field
    Block : Set ℓG
    leafOf : G → Block
    sameLeaf : G → G → Bool
    sameLeaf-reflexive : (g : G) → sameLeaf g g ≡ true

record ExplodedPartitionReceipt
  (P : PartitionSurface G)
  (xs : ExplodedTransform G) : Set (lsuc ℓG) where
  field
    atomBlock : AtomicTransform G → PartitionSurface.Block P
    supportCoherent :
      (a : AtomicTransform G) → (g : G) →
      support a g ≡ true →
      PartitionSurface.sameLeaf P g g ≡ true

------------------------------------------------------------------------
-- Scale tower: coarse maps commute with involution and dynamics.

record ScaleSystem
  (ℓG ℓC ℓU : Level) : Set (lsuc (ℓG ⊔ ℓC ⊔ ℓU)) where
  field
    Geometry : Set ℓG
    Channel : Set ℓC
    Control : Set ℓU
    step : State Geometry Channel → Control → State Geometry Channel

record ScaleMap
  (fine coarse : ScaleSystem ℓG ℓC ℓU) :
  Set (lsuc (ℓG ⊔ ℓC ⊔ ℓU)) where
  private
    module F = ScaleSystem fine
    module K = ScaleSystem coarse
  field
    coarseState : State F.Geometry F.Channel → State K.Geometry K.Channel
    coarseControl : F.Control → K.Control
    commutesWithInvolution :
      (s : State F.Geometry F.Channel) →
      (g : K.Geometry) → (c : K.Channel) →
      coarseState (ιS s) g c ≡ ιS (coarseState s) g c
    commutesWithDynamics :
      (s : State F.Geometry F.Channel) → (u : F.Control) →
      coarseState (F.step s u)
      ≡ K.step (coarseState s) (coarseControl u)

------------------------------------------------------------------------
-- Geometric controls and MDL selection interface.

record GeometricControl (G : Set ℓG) : Set ℓG where
  field
    treeDepth : Nat
    referenceLag : Nat
    transform : ExplodedTransform G
    sideCost : Nat

open GeometricControl public

infix 4 _≤_
data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

totalDescriptionLength :
  ∀ {ℓX} {X : Set ℓX} →
  (X → Nat) → GeometricControl G → X → Nat
totalDescriptionLength residualCost control residual =
  sideCost control + residualCost residual

record MDLChoice
  {ℓX : Level} {X : Set ℓX}
  (residualCost : X → Nat)
  (candidate : GeometricControl G → X)
  (chosen : GeometricControl G) : Set (ℓG ⊔ ℓX) where
  field
    minimal :
      (other : GeometricControl G) →
      totalDescriptionLength residualCost chosen (candidate chosen)
      ≤ totalDescriptionLength residualCost other (candidate other)

------------------------------------------------------------------------
-- Explicit non-promotion gate for the analytic universality statement.

record UniversalityReceipt (G : Set ℓG) : Set (lsuc ℓG) where
  field
    TargetTransform : Set ℓG
    Tolerance : Set ℓG
    Approximates : ExplodedTransform G → TargetTransform → Tolerance → Set ℓG
    chooseApproximation : TargetTransform → Tolerance → ExplodedTransform G
    approximationWitness :
      (target : TargetTransform) → (ε : Tolerance) →
      Approximates (chooseApproximation target ε) target ε
