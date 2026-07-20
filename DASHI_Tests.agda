module DASHI_Tests where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat
open import Agda.Builtin.Sigma using (Σ; _,_)

open import Base369
open import LogicTlurey
open import Kernel.KAlgebra
open import Ultrametric
open import Contraction
open import ActionMonotonicity

-- Physics closure regression imports. These are qualified imports so the
-- broader public closure namespace cannot shadow the legacy smoke tests.
import DASHI.Physics.MaskedCanonicalizationInvariant
import DASHI.Physics.MaskedBlockOrthogonality
import DASHI.Physics.MaskedOperatorInvariants
import DASHI.Physics.MaskedCone
import DASHI.Physics.LorentzianCoreClosure
import DASHI.Physics.GlobalDimensionUniqueness
import DASHI.Physics.FiniteToContinuumGeometry
import DASHI.Physics.BianchiLovelockCompletion
import DASHI.Physics.CliffordRepresentationCompletion
import DASHI.Physics.SpinDoubleCoverCompletion
import DASHI.Physics.CCRContinuumCompletion
import DASHI.Physics.UnitaryCompletion
import DASHI.Physics.StandardModelUniqueness
import DASHI.Physics.FullPhysicsClosure
import DASHI.Physics.ClosureOnAssumption

------------------------------------------------------------------------
-- Base369 regression tests
------------------------------------------------------------------------

rotateTri³-id : ∀ t → spin 3 rotateTri t ≡ t
rotateTri³-id tri-low  = refl
rotateTri³-id tri-mid  = refl
rotateTri³-id tri-high = refl

triXor-comm : ∀ a b → triXor a b ≡ triXor b a
triXor-comm tri-low  tri-low  = refl
triXor-comm tri-low  tri-mid  = refl
triXor-comm tri-low  tri-high = refl
triXor-comm tri-mid  tri-low  = refl
triXor-comm tri-mid  tri-mid  = refl
triXor-comm tri-mid  tri-high = refl
triXor-comm tri-high tri-low  = refl
triXor-comm tri-high tri-mid  = refl
triXor-comm tri-high tri-high = refl

------------------------------------------------------------------------
-- Tlurey trace tests
------------------------------------------------------------------------

next⁴-test : ∀ s → spin 4 next s ≡ s
next⁴-test = next⁴

trace-len-test : ∀ n s → length (StageTrace n s) ≡ n
trace-len-test = StageTrace-length

------------------------------------------------------------------------
-- Kernel algebra tests
------------------------------------------------------------------------

K-id : ∀ {X : Set} → Kernel {X}
K-id {X} = record
  { K = λ s → s
  ; involutive-respecting = λ s → refl
  }

K-neg : ∀ {X : Set} → Kernel {X}
K-neg {X} = record
  { K = ι
  ; involutive-respecting = λ s → refl
  }

K-neg2-pointwise : ∀ {X : Set} (s : State X) (x : X) →
  Kernel.K (K-neg {X}) (Kernel.K (K-neg {X}) s) x ≡ s x
K-neg2-pointwise s x = ι²-id s x

------------------------------------------------------------------------
-- Contraction / monotone-action interface smoke tests
------------------------------------------------------------------------

postulate
  X : Set
  U : Ultrametric X
  f : X → X
  cf : Contractive U f
  x y : X

contraction-smoke = Contractive.contraction cf x y

postulate
  X1 : Set
  K1 : State X1 → State X1
  A1 : State X1 → Nat
  M : Monotone K1 A1
  s1 : State X1

monotone-smoke = Monotone.monotone M s1
