module DASHI.Physics.YangMills.BalabanYM4DifferentiatedKKTSourceSupportExact where

-- Tadeusz Bałaban, "The Variational Problem and Background Fields in
-- Renormalization Group Method for Lattice Gauge Theories", CMP 102 (1985),
-- 277--309. DOI: 10.1007/BF01229381.
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", CMP 99 (1985), 389--434. DOI: 10.1007/BF01240355.
-- Franco Brezzi, "On the Existence, Uniqueness and Approximation of
-- Saddle-Point Problems Arising from Lagrangian Multipliers", RAIRO Analyse
-- Numerique 8 (1974). No DOI assigned to the cited article.

open import Data.Rational.Base using (0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTAdmissibleProjectorExact as State
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockGreenExact as Block
import DASHI.Physics.YangMills.BalabanYM4DifferentiatedKKTMinimizerExact as Diff

record PhysicalDifferentiatedKKTSourceSupport {Multiplier : Set}
    (dataSet : Diff.DifferentiatedKKTMinimizerData Multiplier) : Set₁ where
  field
    StateRemote : State.State → Set
    MultiplierRemote : Multiplier → Set
    stateSourceVanishesRemotely : ∀ coordinate → StateRemote coordinate →
      Block.statePart (Diff.stateSource dataSet) coordinate ≡ 0ℚ
    multiplierSourceVanishesRemotely : ∀ row → MultiplierRemote row →
      Block.multiplierPart (Diff.stateSource dataSet) row ≡ 0ℚ
open PhysicalDifferentiatedKKTSourceSupport public

sameSupportedSourceSolvesKKT :
  ∀ {Multiplier} {dataSet : Diff.DifferentiatedKKTMinimizerData Multiplier} →
  PhysicalDifferentiatedKKTSourceSupport dataSet →
  Block.PointwiseKKTBlockEquality
    (Diff.differentiatedPair dataSet)
    (Block.solveKKTBlock (Diff.greenData dataSet) (Diff.stateSource dataSet))
sameSupportedSourceSolvesKKT {dataSet = dataSet} _ =
  Diff.differentiatedPairIsKKTGreenSolve dataSet

sameSupportedSourceStateSolution :
  ∀ {Multiplier} {dataSet : Diff.DifferentiatedKKTMinimizerData Multiplier} →
  PhysicalDifferentiatedKKTSourceSupport dataSet →
  ∀ coordinate →
  Block.statePart (Diff.differentiatedPair dataSet) coordinate
  ≡ Block.statePart
      (Block.solveKKTBlock (Diff.greenData dataSet) (Diff.stateSource dataSet)) coordinate
sameSupportedSourceStateSolution {dataSet = dataSet} _ =
  Diff.differentiatedStateIsKKTGreenState dataSet

ym4DifferentiatedKKTSourceSupportSameObjectLevel : ProofLevel
ym4DifferentiatedKKTSourceSupportSameObjectLevel = machineChecked

ym4LiteralDifferentiatedKKTPhysicalSourceSupportLevel : ProofLevel
ym4LiteralDifferentiatedKKTPhysicalSourceSupportLevel = conditional
