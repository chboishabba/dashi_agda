module DASHI.Physics.Common.FiniteProjectionOffDiagonalExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Volker Bach, Thomas Chen, Jurg Frohlich and Israel Michael Sigal,
-- "Smooth Feshbach Map and Operator-Theoretic Renormalization Group
-- Methods", Journal of Functional Analysis 203 (2003), 44--92.
-- DOI: 10.1016/S0022-1236(03)00057-0.
--
-- Tosio Kato and Gustavo Ponce,
-- "Commutator Estimates and the Euler and Navier--Stokes Equations",
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
-- DOI: 10.1002/cpa.3160410704.
--
-- DASHI CONTRIBUTION
--
-- Give one exact two-sector rational carrier in which the following objects
-- are literally the same off-diagonal algebra:
--
--   * a projection commutator [P,A];
--   * coarse-to-fine and fine-to-coarse leakage blocks;
--   * the coupling B entering a Schur/Feshbach reduction.
--
-- This is shared finite algebra only.  It supplies neither a Littlewood--Paley
-- commutator estimate nor a physical RG bound on the Yang--Mills coupling.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; -_; _*_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong₂)

record SectorVector : Set where
  constructor sectorVector
  field
    retained : ℚ
    eliminated : ℚ

open SectorVector public

record BlockOperator : Set where
  constructor blockOperator
  field
    retainedRetained : ℚ
    retainedEliminated : ℚ
    eliminatedRetained : ℚ
    eliminatedEliminated : ℚ

open BlockOperator public

vectorAdd : SectorVector → SectorVector → SectorVector
vectorAdd left right =
  sectorVector
    (retained left + retained right)
    (eliminated left + eliminated right)

vectorSubtract : SectorVector → SectorVector → SectorVector
vectorSubtract left right =
  sectorVector
    (retained left - retained right)
    (eliminated left - eliminated right)

zeroVector : SectorVector
zeroVector = sectorVector 0ℚ 0ℚ

applyBlock : BlockOperator → SectorVector → SectorVector
applyBlock operator vector =
  sectorVector
    (retainedRetained operator * retained vector
      + retainedEliminated operator * eliminated vector)
    (eliminatedRetained operator * retained vector
      + eliminatedEliminated operator * eliminated vector)

retainProjection : SectorVector → SectorVector
retainProjection vector = sectorVector (retained vector) 0ℚ

eliminateProjection : SectorVector → SectorVector
eliminateProjection vector = sectorVector 0ℚ (eliminated vector)

diagonalPart : BlockOperator → BlockOperator
diagonalPart operator =
  blockOperator
    (retainedRetained operator)
    0ℚ
    0ℚ
    (eliminatedEliminated operator)

offDiagonalPart : BlockOperator → BlockOperator
offDiagonalPart operator =
  blockOperator
    0ℚ
    (retainedEliminated operator)
    (eliminatedRetained operator)
    0ℚ

projectionCommutator : BlockOperator → SectorVector → SectorVector
projectionCommutator operator vector =
  vectorSubtract
    (retainProjection (applyBlock operator vector))
    (applyBlock operator (retainProjection vector))

retainedLeakage : BlockOperator → SectorVector → ℚ
retainedLeakage operator vector =
  retainedEliminated operator * eliminated vector

eliminatedLeakage : BlockOperator → SectorVector → ℚ
eliminatedLeakage operator vector =
  eliminatedRetained operator * retained vector

projectionCommutatorExact :
  (operator : BlockOperator) →
  (vector : SectorVector) →
  projectionCommutator operator vector
  ≡ sectorVector
      (retainedLeakage operator vector)
      (- eliminatedLeakage operator vector)
projectionCommutatorExact
    (blockOperator a b c d)
    (sectorVector x y) =
  cong₂ sectorVector
    (ℚRing.solve-∀ a b c d x y)
    (ℚRing.solve-∀ a b c d x y)

blockDecompositionExact :
  (operator : BlockOperator) →
  (vector : SectorVector) →
  applyBlock operator vector
  ≡ vectorAdd
      (applyBlock (diagonalPart operator) vector)
      (applyBlock (offDiagonalPart operator) vector)
blockDecompositionExact
    (blockOperator a b c d)
    (sectorVector x y) =
  cong₂ sectorVector
    (ℚRing.solve-∀ a b c d x y)
    (ℚRing.solve-∀ a b c d x y)

vectorNormSq : SectorVector → ℚ
vectorNormSq vector =
  retained vector * retained vector
  + eliminated vector * eliminated vector

offDiagonalLeakageSq : BlockOperator → SectorVector → ℚ
offDiagonalLeakageSq operator vector =
  retainedLeakage operator vector * retainedLeakage operator vector
  + eliminatedLeakage operator vector * eliminatedLeakage operator vector

projectionCommutatorNormSqExact :
  (operator : BlockOperator) →
  (vector : SectorVector) →
  vectorNormSq (projectionCommutator operator vector)
  ≡ offDiagonalLeakageSq operator vector
projectionCommutatorNormSqExact
    (blockOperator a b c d)
    (sectorVector x y) =
  ℚRing.solve-∀ a b c d x y

projectionCommutesWhenOffDiagonalZero :
  (a d : ℚ) →
  (vector : SectorVector) →
  projectionCommutator (blockOperator a 0ℚ 0ℚ d) vector
  ≡ zeroVector
projectionCommutesWhenOffDiagonalZero
    a d (sectorVector x y) =
  cong₂ sectorVector
    (ℚRing.solve-∀ a d x y)
    (ℚRing.solve-∀ a d x y)

symmetricCouplingOperator : ℚ → ℚ → ℚ → BlockOperator
symmetricCouplingOperator retainedBlock coupling eliminatedBlock =
  blockOperator retainedBlock coupling coupling eliminatedBlock

symmetricCouplingLeakageSqExact :
  (retainedBlock coupling eliminatedBlock : ℚ) →
  (vector : SectorVector) →
  offDiagonalLeakageSq
    (symmetricCouplingOperator retainedBlock coupling eliminatedBlock)
    vector
  ≡ coupling * coupling * vectorNormSq vector
symmetricCouplingLeakageSqExact
    retainedBlock coupling eliminatedBlock
    (sectorVector x y) =
  ℚRing.solve-∀ retainedBlock coupling eliminatedBlock x y

canonicalLeakageOperator : BlockOperator
canonicalLeakageOperator = blockOperator 2 3 5 7

canonicalLeakageVector : SectorVector
canonicalLeakageVector = sectorVector 11 13

canonicalProjectionCommutator :
  projectionCommutator canonicalLeakageOperator canonicalLeakageVector
  ≡ sectorVector 39 (- 55)
canonicalProjectionCommutator = refl
