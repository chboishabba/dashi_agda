module DASHI.Algebra.Quantum.NVSpinOneC3HamiltonianObstructionExact where

-- Exact finite obstruction for cyclic permutation of the NV spin-one labels.
-- Mathematical model: Sz^2 has spectrum (1,0,1) in the conventional
-- ordered basis (+1,0,-1). The scale factor D is intentionally omitted.
-- This does NOT deny other C3 symmetries on other physical subspaces.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≟_)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.Quantum.NVSpinOneC3ChartAdapter as Chart

-- Convention: c0 = +1, c1 = 0, c2 = -1.
szSquaredEigenvalue : C3.C3 → Nat
szSquaredEigenvalue C3.c0 = 1
szSquaredEigenvalue C3.c1 = 0
szSquaredEigenvalue C3.c2 = 1

-- Cyclic permutation sends |+1> to |0>, changing Sz^2 energy.
c3CycleChangesSzSquared :
  szSquaredEigenvalue (Chart.cycleLabel C3.c0) ≡ 0
c3CycleChangesSzSquared = refl

originalPositiveSzSquared :
  szSquaredEigenvalue C3.c0 ≡ 1
originalPositiveSzSquared = refl

-- A required energy-preservation witness is constructively impossible.
zeroNotOne : zero ≡ suc zero → ⊥
zeroNotOne ()

c3CycleNotSzSquaredInvariant :
  (∀ x → szSquaredEigenvalue (Chart.cycleLabel x)
       ≡ szSquaredEigenvalue x) → ⊥
c3CycleNotSzSquaredInvariant preserves =
  zeroNotOne (preserves C3.c0)

-- The obstruction holds for this nondegenerate symbolic Sz^2 profile.
-- It does not assert it for D = 0, a driven effective Floquet operator,
-- a differently chosen three-level subspace, or other Hamiltonians.

-- By contrast, the reflection exchanging the degenerate +1/-1 levels
-- preserves the symbolic Sz² spectrum.  It has order two, not three.
swapPlusMinus : C3.C3 → C3.C3
swapPlusMinus C3.c0 = C3.c2
swapPlusMinus C3.c1 = C3.c1
swapPlusMinus C3.c2 = C3.c0

swapPlusMinusInvolutive :
  ∀ x → swapPlusMinus (swapPlusMinus x) ≡ x
swapPlusMinusInvolutive C3.c0 = refl
swapPlusMinusInvolutive C3.c1 = refl
swapPlusMinusInvolutive C3.c2 = refl

swapPlusMinusPreservesSzSquared :
  ∀ x → szSquaredEigenvalue (swapPlusMinus x)
        ≡ szSquaredEigenvalue x
swapPlusMinusPreservesSzSquared C3.c0 = refl
swapPlusMinusPreservesSzSquared C3.c1 = refl
swapPlusMinusPreservesSzSquared C3.c2 = refl
