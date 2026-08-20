module DASHI.Physics.YangMills.BalabanClayT4WilsonOneLoopSignCharacterProjectionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977. DOI: 10.1007/978-1-4684-9458-7.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- Make the C2^4 sign action on the ACTUAL generated Brillouin cells explicit
-- and compose it with the Walsh characters on Subset4.  For any rational
-- scalar box function invariant under that sign action, every nontrivial
-- character projection vanishes exactly BEFORE interval majorization.
--
-- The physical Wilson/ghost/Haar integrand is not silently declared invariant
-- here: its literal joint-(k,p) equivariance is a separate source theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4HyperoctahedralGridOrbitExact as Orbit

flipIf : Bool → Grid.IntervalCell → Grid.IntervalCell
flipIf false interval = interval
flipIf true interval = Orbit.flipInterval interval

outerFlipIf : ∀ bit interval →
  Orbit.outer (flipIf bit interval) ≡ Orbit.outer interval
outerFlipIf false interval = refl
outerFlipIf true interval = Orbit.outerFlipExact interval

signAct : Cube.Subset4 → Grid.GridCell4 → Grid.GridCell4
signAct signs (Grid.gridCell4 a b c d) = Grid.gridCell4
  (flipIf (Cube.contains Cube.slot0 signs) a)
  (flipIf (Cube.contains Cube.slot1 signs) b)
  (flipIf (Cube.contains Cube.slot2 signs) c)
  (flipIf (Cube.contains Cube.slot3 signs) d)

signActPreservesGeometricOrbit : ∀ signs cell →
  Orbit.geometricOrbit (signAct signs cell) ≡ Orbit.geometricOrbit cell
signActPreservesGeometricOrbit signs (Grid.gridCell4 a b c d)
  rewrite outerFlipIf (Cube.contains Cube.slot0 signs) a
        | outerFlipIf (Cube.contains Cube.slot1 signs) b
        | outerFlipIf (Cube.contains Cube.slot2 signs) c
        | outerFlipIf (Cube.contains Cube.slot3 signs) d
  = refl

signCharacterProjection :
  Cube.Subset4 → (Grid.GridCell4 → ℚ) → Grid.GridCell4 → ℚ
signCharacterProjection frequency value cell =
  Sums.sumRational Cube.allSubsets4
    (λ signs → Walsh.walshCharacter frequency signs * value (signAct signs cell))

record SignInvariantAt (value : Grid.GridCell4 → ℚ) (cell : Grid.GridCell4) : Set where
  field
    invariant : ∀ signs → value (signAct signs cell) ≡ value cell
open SignInvariantAt public

projectionCongToPureSector :
  ∀ frequency value cell →
  SignInvariantAt value cell →
  signCharacterProjection frequency value cell
  ≡ Walsh.characterSectorOrbitSum frequency (value cell)
projectionCongToPureSector frequency value cell data =
  Sums.sumRationalCong
    Cube.allSubsets4
    (λ signs → Walsh.walshCharacter frequency signs * value (signAct signs cell))
    (Walsh.characterSector frequency (value cell))
    (λ signs →
      cong
        (λ selected → Walsh.walshCharacter frequency signs * selected)
        (invariant data signs))

nontrivialSignCharacterProjectionVanishes :
  ∀ {frequency} → Walsh.NontrivialFrequency frequency →
  ∀ value cell → SignInvariantAt value cell →
  signCharacterProjection frequency value cell ≡ 0ℚ
nontrivialSignCharacterProjectionVanishes nontrivial value cell data =
  trans
    (projectionCongToPureSector _ value cell data)
    (Walsh.nontrivialCharacterSectorOrbitSumVanishes
      nontrivial (value cell))

signActionGeometryLevel : ProofLevel
signActionGeometryLevel = machineChecked

signCharacterProjectionLevel : ProofLevel
signCharacterProjectionLevel = machineChecked

nontrivialSignCharacterProjectionCancellationLevel : ProofLevel
nontrivialSignCharacterProjectionCancellationLevel = machineChecked

-- Source-facing leaf: instantiate SignInvariantAt for the literal scalar
-- Wilson/ghost/Haar regular integrand under the JOINT action on loop and
-- external momenta.  This is intentionally separate from the finite character
-- algebra above.
literalWilsonOneLoopJointSignInvarianceLevel : ProofLevel
literalWilsonOneLoopJointSignInvarianceLevel = conditional
