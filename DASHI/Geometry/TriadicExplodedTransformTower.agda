module DASHI.Geometry.TriadicExplodedTransformTower where

-- A constructive, application-independent geometry layer for the DASHI
-- ternary/involution formalism.
--
-- Scope discipline:
-- * proved here: involution laws, pullback equivariance, atomic/exploded
--   transform equivariance, and the typed renormalisation/MDL interfaces;
-- * not asserted here: analytic universality of piecewise-affine maps,
--   convergence to a continuum warp, or codec-rate superiority.
--   Those require an explicit metric, approximation theorem, and empirical
--   receipts and therefore remain behind UniversalityReceipt below.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Primitive using (Level; _⊔_; lsuc)

private
  variable
    ℓG ℓC ℓU ℓS : Level
    G : Set ℓG
    C : Set ℓC

cong :
  ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} →
  (f : A → B) →
  ∀ {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

------------------------------------------------------------------------
-- Primitive balanced ternary carrier and involution


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
-- Geometry acts on indices by pullback and therefore commutes with sign.

Warp : Set ℓG → Set ℓG
Warp G = G → G

pullback : Warp G → State G C → State G C
pullback w s g c = s (w g) c

pullback-commutes-with-involution :
  (w : Warp G) →
  (s : State G C) →
  (g : G) →
  (c : C) →
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

applyAtomic : AtomicTransform G → State G C → State G C
applyAtomic a s g c with support a g
... | true = s (localWarp a g) c
... | false = s g c

applyAtomic-commutes-with-involution :
  (a : AtomicTransform G) →
  (s : State G C) →
  (g : G) →
  (c : C) →
  ιS (applyAtomic a s) g c ≡ applyAtomic a (ιS s) g c
applyAtomic-commutes-with-involution a s g c with support a g
... | true = refl
... | false = refl

-- An exploded transform is an ordered finite family of atomic transforms.
-- Disjoint-support and partition-tree coherence are represented separately
-- below, because they are properties/receipts rather than required to define
-- the executable action.

ExplodedTransform : Set ℓG → Set ℓG
ExplodedTransform G = List (AtomicTransform G)

applyExploded : ExplodedTransform G → State G C → State G C
applyExploded [] s = s
applyExploded (a ∷ as) s = applyExploded as (applyAtomic a s)

applyExploded-commutes-with-involution :
  (xs : ExplodedTransform G) →
  (s : State G C) →
  (g : G) →
  (c : C) →
  ιS (applyExploded xs s) g c ≡ applyExploded xs (ιS s) g c
applyExploded-commutes-with-involution [] s g c = refl
applyExploded-commutes-with-involution (a ∷ as) s g c =
  let
    atomicStep :
      ιS (applyAtomic a s) g c ≡ applyAtomic a (ιS s) g c
    atomicStep = applyAtomic-commutes-with-involution a s g c
  in
  applyExploded-commutes-with-involution as (applyAtomic a s) g c

------------------------------------------------------------------------
-- Partition-tree and recognisability interfaces.

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
    supportStaysInLeaf :
      (a : AtomicTransform G) →
      (g : G) →
      support a g ≡ true →
      PartitionSurface.sameLeaf P g g ≡ true

------------------------------------------------------------------------
-- Scale tower: coarse maps commute with involution and dynamics.

record ScaleSystem : Set (lsuc (ℓG ⊔ ℓC ⊔ ℓU)) where
  field
    Geometry : Set ℓG
    Channel : Set ℓC
    Control : Set ℓU
    step : State Geometry Channel → Control → State Geometry Channel

record ScaleMap
  (fine coarse : ScaleSystem {ℓG} {ℓC} {ℓU}) :
  Set (lsuc (ℓG ⊔ ℓC ⊔ ℓU)) where
  private
    module F = ScaleSystem fine
    module K = ScaleSystem coarse
  field
    coarseState : State F.Geometry F.Channel → State K.Geometry K.Channel
    coarseControl : F.Control → K.Control

    commutesWithInvolution :
      (s : State F.Geometry F.Channel) →
      (g : K.Geometry) →
      (c : K.Channel) →
      coarseState (ιS s) g c ≡ ιS (coarseState s) g c

    commutesWithDynamics :
      (s : State F.Geometry F.Channel) →
      (u : F.Control) →
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

residualCost :
  ∀ {ℓX} {X : Set ℓX} →
  (X → Nat) → X → Nat
residualCost cost x = cost x

totalDescriptionLength :
  ∀ {ℓX} {X : Set ℓX} →
  (X → Nat) →
  GeometricControl G →
  X →
  Nat
totalDescriptionLength cost control residual =
  sideCost control + residualCost cost residual

record MDLChoice
  {ℓX : Level}
  {X : Set ℓX}
  (cost : X → Nat)
  (candidate : GeometricControl G → X)
  (chosen : GeometricControl G) : Set (ℓG ⊔ ℓX) where
  field
    minimal :
      (other : GeometricControl G) →
      totalDescriptionLength cost chosen (candidate chosen)
      ≡ totalDescriptionLength cost other (candidate other)
      →
      totalDescriptionLength cost chosen (candidate chosen)
      ≡ totalDescriptionLength cost other (candidate other)

-- This record is deliberately a gate, not a theorem.  A consumer claiming
-- universal approximation must provide its domain metric/tolerance relation,
-- a refinement construction, and a witness for every target transform.
record UniversalityReceipt (G : Set ℓG) : Set (lsuc ℓG) where
  field
    TargetTransform : Set ℓG
    Tolerance : Set ℓG
    Approximates : ExplodedTransform G → TargetTransform → Tolerance → Set ℓG
    approximationWitness :
      (target : TargetTransform) →
      (ε : Tolerance) →
      (xs : ExplodedTransform G) →
      Approximates xs target ε
