module DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List)
import Data.Nat.Properties as NatProp

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
open Cube using (_∈_; NoDuplicates)
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact max-coordinate outer-cube count for shell n.
--
-- The far-high Bernstein argument needs only that shell support is contained in
-- |k|_infinity <= 2^n.  We therefore count that literal duplicate-free cube
-- directly and do not transport a Euclidean-annulus theorem.
------------------------------------------------------------------------

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc n) = pow2 n + pow2 n

infinityCubeModes : Nat → List Z3.FourierMode
infinityCubeModes n = Cube.cutoffModes (pow2 n)

infinityCubeSideCount : Nat → Nat
infinityCubeSideCount n = Cube.intervalCardinality (pow2 n)

infinityCubeModeCount : Nat → Nat
infinityCubeModeCount n = Cube.cutoffCubeCardinality (pow2 n)

infinityCubeModeCountMeaning : ∀ n →
  infinityCubeModeCount n
  ≡ infinityCubeSideCount n
      * (infinityCubeSideCount n * infinityCubeSideCount n)
infinityCubeModeCountMeaning n = refl

literalInfinityCubeLength : ∀ n →
  Cube.length (infinityCubeModes n) ≡ infinityCubeModeCount n
literalInfinityCubeLength n = Cube.literalCutoffCubeLength (pow2 n)

literalInfinityCubeNoDuplicates : ∀ n →
  NoDuplicates (infinityCubeModes n)
literalInfinityCubeNoDuplicates n =
  Cube.cutoffModeEnumerationNoDuplicates (pow2 n)

pow2Positive : ∀ n → 1 Cube.≤ᴺ pow2 n
pow2Positive zero = Cube.s≤s Cube.z≤n
pow2Positive (suc n) =
  Cube.≤ᴺ-trans (pow2Positive n) (Cube.≤ᴺ-+-right (pow2 n) (Cube.≤ᴺ-refl (pow2 n)))

infinityCubeSideCountBound : ∀ n → infinityCubeSideCount n Cube.≤ᴺ 3 * pow2 n
infinityCubeSideCountBound n =
  Cube.intervalCardinalityBound (pow2 n) (pow2Positive n)

open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open Relation.Binary.PropositionalEquality.≡-Reasoning

cube3Equiv : ∀ N → (3 * N) * ((3 * N) * (3 * N)) ≡ 27 * (N * (N * N))
cube3Equiv N = begin
  (3 * N) * ((3 * N) * (3 * N))
    ≡⟨ NatProp.*-assoc 3 N ((3 * N) * (3 * N)) ⟩
  3 * (N * ((3 * N) * (3 * N)))
    ≡⟨ cong (λ x → 3 * (N * x)) (NatProp.*-assoc 3 N (3 * N)) ⟩
  3 * (N * (3 * (N * (3 * N))))
    ≡⟨ cong (λ x → 3 * x) (sym (NatProp.*-assoc N 3 (N * (3 * N)))) ⟩
  3 * ((N * 3) * (N * (3 * N)))
    ≡⟨ cong (λ x → 3 * (x * (N * (3 * N)))) (NatProp.*-comm N 3) ⟩
  3 * ((3 * N) * (N * (3 * N)))
    ≡⟨ cong (λ x → 3 * x) (NatProp.*-assoc 3 N (N * (3 * N))) ⟩
  3 * (3 * (N * (N * (3 * N))))
    ≡⟨ sym (NatProp.*-assoc 3 3 (N * (N * (3 * N)))) ⟩
  9 * (N * (N * (3 * N)))
    ≡⟨ cong (λ x → 9 * (N * (N * x))) (NatProp.*-comm 3 N) ⟩
  9 * (N * (N * (N * 3)))
    ≡⟨ cong (λ x → 9 * (N * x)) (sym (NatProp.*-assoc N N 3)) ⟩
  9 * (N * ((N * N) * 3))
    ≡⟨ cong (λ x → 9 * x) (sym (NatProp.*-assoc N (N * N) 3)) ⟩
  9 * ((N * (N * N)) * 3)
    ≡⟨ cong (λ x → 9 * x) (NatProp.*-comm (N * (N * N)) 3) ⟩
  9 * (3 * (N * (N * N)))
    ≡⟨ sym (NatProp.*-assoc 9 3 (N * (N * N))) ⟩
  27 * (N * (N * N))
  ∎

coarseTwentySevenTimesDyadicCubeBound :
  ∀ n → infinityCubeModeCount n Cube.≤ᴺ 27 * (pow2 n * (pow2 n * pow2 n))
coarseTwentySevenTimesDyadicCubeBound n =
  Cube.≤ᴺ-substRight
    (cube3Equiv (pow2 n))
    (Cube.≤ᴺ-*-mono (infinityCubeSideCountBound n)
      (Cube.≤ᴺ-*-mono (infinityCubeSideCountBound n) (infinityCubeSideCountBound n)))

record InfinityShellSupport (n : Nat) : Set₁ where
  field
    shellModes : List Z3.FourierMode

    -- The shell may use any exact annular profile, but every listed mode must
    -- belong to the counted outer cube.
    shellContainedInOuterCube : ∀ k →
      k ∈ shellModes →
      k ∈ infinityCubeModes n

    shellNoDuplicates : NoDuplicates shellModes

open InfinityShellSupport public

infinityShellModeCountLevel : ProofLevel
infinityShellModeCountLevel = machineChecked

coarseTwentySevenTimesDyadicCubeBoundLevel : ProofLevel
coarseTwentySevenTimesDyadicCubeBoundLevel = machineChecked
