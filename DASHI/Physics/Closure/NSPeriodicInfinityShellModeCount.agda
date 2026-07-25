module DASHI.Physics.Closure.NSPeriodicInfinityShellModeCount where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
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
  Cube.NoDuplicates (infinityCubeModes n)
literalInfinityCubeNoDuplicates n =
  Cube.cutoffModeEnumerationNoDuplicates (pow2 n)

record InfinityShellSupport (n : Nat) : Set₁ where
  field
    shellModes : List Z3.FourierMode

    -- The shell may use any exact annular profile, but every listed mode must
    -- belong to the counted outer cube.
    shellContainedInOuterCube : ∀ k →
      Cube._∈_ k shellModes →
      Cube._∈_ k (infinityCubeModes n)

    shellNoDuplicates : Cube.NoDuplicates shellModes

open InfinityShellSupport public

infinityShellModeCountLevel : ProofLevel
infinityShellModeCountLevel = machineChecked

coarseTwentySevenTimesDyadicCubeBoundLevel : ProofLevel
coarseTwentySevenTimesDyadicCubeBoundLevel = conditional
