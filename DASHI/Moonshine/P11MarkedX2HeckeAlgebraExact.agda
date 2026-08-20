module DASHI.Moonshine.P11MarkedX2HeckeAlgebraExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Annals of Mathematics Studies 108,
-- Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Stress-test the CORRECTED source-native marked X(2) operators reconstructed
-- from quaternion congruence-theta counts.  We do not preserve any property of
-- the old hand-built model by assumption.
--
-- Results:
--
--   * marked T3 and T5 commute on all 25 matrix entries;
--   * both marked adjacency matrices are symmetric;
--   * T3^2 - 3 I and T5^2 - 5 I are entrywise Nat-valued;
--   * their residual row sums are 13 and 31, the expected sigma_1(9),
--     sigma_1(25) constant-line degrees.
--
-- Corrected residuals:
--
-- T9 =
-- [1 3 3 3 3]
-- [3 1 3 3 3]
-- [3 3 1 3 3]
-- [3 3 3 1 3]
-- [3 3 3 3 1]
--
-- T25 =
-- [7 3 7 7 7]
-- [3 7 7 7 7]
-- [7 7 3 7 7]
-- [7 7 7 3 7]
-- [7 7 7 7 3].
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FullLevel2DeckHeckeEquivarianceExact as Deck
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked

indicator : Fine.P11Fine5 → Fine.P11Fine5 → Nat
indicator Fine.a0 Fine.a0 = 1
indicator Fine.a0 _ = 0
indicator Fine.a1 Fine.a1 = 1
indicator Fine.a1 _ = 0
indicator Fine.b0 Fine.b0 = 1
indicator Fine.b0 _ = 0
indicator Fine.b1 Fine.b1 = 1
indicator Fine.b1 _ = 0
indicator Fine.b2 Fine.b2 = 1
indicator Fine.b2 _ = 0

pathCount :
  Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5 →
  Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5 →
  Fine.P11Fine5 → Fine.P11Fine5 → Nat
pathCount first second source target =
  Positive.twoStepOperator first second (indicator target) source

------------------------------------------------------------------------
-- T3 and T5 commute entrywise.
------------------------------------------------------------------------

markedT3T5CommuteEntry :
  (source target : Fine.P11Fine5) →
  pathCount Marked.MarkedT3Positive Marked.MarkedT5Positive source target
  ≡ pathCount Marked.MarkedT5Positive Marked.MarkedT3Positive source target
markedT3T5CommuteEntry Fine.a0 Fine.a0 = refl
markedT3T5CommuteEntry Fine.a0 Fine.a1 = refl
markedT3T5CommuteEntry Fine.a0 Fine.b0 = refl
markedT3T5CommuteEntry Fine.a0 Fine.b1 = refl
markedT3T5CommuteEntry Fine.a0 Fine.b2 = refl
markedT3T5CommuteEntry Fine.a1 Fine.a0 = refl
markedT3T5CommuteEntry Fine.a1 Fine.a1 = refl
markedT3T5CommuteEntry Fine.a1 Fine.b0 = refl
markedT3T5CommuteEntry Fine.a1 Fine.b1 = refl
markedT3T5CommuteEntry Fine.a1 Fine.b2 = refl
markedT3T5CommuteEntry Fine.b0 Fine.a0 = refl
markedT3T5CommuteEntry Fine.b0 Fine.a1 = refl
markedT3T5CommuteEntry Fine.b0 Fine.b0 = refl
markedT3T5CommuteEntry Fine.b0 Fine.b1 = refl
markedT3T5CommuteEntry Fine.b0 Fine.b2 = refl
markedT3T5CommuteEntry Fine.b1 Fine.a0 = refl
markedT3T5CommuteEntry Fine.b1 Fine.a1 = refl
markedT3T5CommuteEntry Fine.b1 Fine.b0 = refl
markedT3T5CommuteEntry Fine.b1 Fine.b1 = refl
markedT3T5CommuteEntry Fine.b1 Fine.b2 = refl
markedT3T5CommuteEntry Fine.b2 Fine.a0 = refl
markedT3T5CommuteEntry Fine.b2 Fine.a1 = refl
markedT3T5CommuteEntry Fine.b2 Fine.b0 = refl
markedT3T5CommuteEntry Fine.b2 Fine.b1 = refl
markedT3T5CommuteEntry Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Fine marked adjacencies are ordinary symmetric correspondences.
------------------------------------------------------------------------

markedT3Symmetric :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT3Positive x y
  ≡ Deck.edgeMultiplicity Marked.MarkedT3Positive y x
markedT3Symmetric Fine.a0 Fine.a0 = refl
markedT3Symmetric Fine.a0 Fine.a1 = refl
markedT3Symmetric Fine.a0 Fine.b0 = refl
markedT3Symmetric Fine.a0 Fine.b1 = refl
markedT3Symmetric Fine.a0 Fine.b2 = refl
markedT3Symmetric Fine.a1 Fine.a0 = refl
markedT3Symmetric Fine.a1 Fine.a1 = refl
markedT3Symmetric Fine.a1 Fine.b0 = refl
markedT3Symmetric Fine.a1 Fine.b1 = refl
markedT3Symmetric Fine.a1 Fine.b2 = refl
markedT3Symmetric Fine.b0 Fine.a0 = refl
markedT3Symmetric Fine.b0 Fine.a1 = refl
markedT3Symmetric Fine.b0 Fine.b0 = refl
markedT3Symmetric Fine.b0 Fine.b1 = refl
markedT3Symmetric Fine.b0 Fine.b2 = refl
markedT3Symmetric Fine.b1 Fine.a0 = refl
markedT3Symmetric Fine.b1 Fine.a1 = refl
markedT3Symmetric Fine.b1 Fine.b0 = refl
markedT3Symmetric Fine.b1 Fine.b1 = refl
markedT3Symmetric Fine.b1 Fine.b2 = refl
markedT3Symmetric Fine.b2 Fine.a0 = refl
markedT3Symmetric Fine.b2 Fine.a1 = refl
markedT3Symmetric Fine.b2 Fine.b0 = refl
markedT3Symmetric Fine.b2 Fine.b1 = refl
markedT3Symmetric Fine.b2 Fine.b2 = refl

markedT5Symmetric :
  (x y : Fine.P11Fine5) →
  Deck.edgeMultiplicity Marked.MarkedT5Positive x y
  ≡ Deck.edgeMultiplicity Marked.MarkedT5Positive y x
markedT5Symmetric Fine.a0 Fine.a0 = refl
markedT5Symmetric Fine.a0 Fine.a1 = refl
markedT5Symmetric Fine.a0 Fine.b0 = refl
markedT5Symmetric Fine.a0 Fine.b1 = refl
markedT5Symmetric Fine.a0 Fine.b2 = refl
markedT5Symmetric Fine.a1 Fine.a0 = refl
markedT5Symmetric Fine.a1 Fine.a1 = refl
markedT5Symmetric Fine.a1 Fine.b0 = refl
markedT5Symmetric Fine.a1 Fine.b1 = refl
markedT5Symmetric Fine.a1 Fine.b2 = refl
markedT5Symmetric Fine.b0 Fine.a0 = refl
markedT5Symmetric Fine.b0 Fine.a1 = refl
markedT5Symmetric Fine.b0 Fine.b0 = refl
markedT5Symmetric Fine.b0 Fine.b1 = refl
markedT5Symmetric Fine.b0 Fine.b2 = refl
markedT5Symmetric Fine.b1 Fine.a0 = refl
markedT5Symmetric Fine.b1 Fine.a1 = refl
markedT5Symmetric Fine.b1 Fine.b0 = refl
markedT5Symmetric Fine.b1 Fine.b1 = refl
markedT5Symmetric Fine.b1 Fine.b2 = refl
markedT5Symmetric Fine.b2 Fine.a0 = refl
markedT5Symmetric Fine.b2 Fine.a1 = refl
markedT5Symmetric Fine.b2 Fine.b0 = refl
markedT5Symmetric Fine.b2 Fine.b1 = refl
markedT5Symmetric Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Corrected prime-square residual multiplicity functions.
------------------------------------------------------------------------

markedT9Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
markedT9Multiplicity Fine.a0 Fine.a0 = 1
markedT9Multiplicity Fine.a0 Fine.a1 = 3
markedT9Multiplicity Fine.a0 Fine.b0 = 3
markedT9Multiplicity Fine.a0 Fine.b1 = 3
markedT9Multiplicity Fine.a0 Fine.b2 = 3
markedT9Multiplicity Fine.a1 Fine.a0 = 3
markedT9Multiplicity Fine.a1 Fine.a1 = 1
markedT9Multiplicity Fine.a1 Fine.b0 = 3
markedT9Multiplicity Fine.a1 Fine.b1 = 3
markedT9Multiplicity Fine.a1 Fine.b2 = 3
markedT9Multiplicity Fine.b0 Fine.a0 = 3
markedT9Multiplicity Fine.b0 Fine.a1 = 3
markedT9Multiplicity Fine.b0 Fine.b0 = 1
markedT9Multiplicity Fine.b0 Fine.b1 = 3
markedT9Multiplicity Fine.b0 Fine.b2 = 3
markedT9Multiplicity Fine.b1 Fine.a0 = 3
markedT9Multiplicity Fine.b1 Fine.a1 = 3
markedT9Multiplicity Fine.b1 Fine.b0 = 3
markedT9Multiplicity Fine.b1 Fine.b1 = 1
markedT9Multiplicity Fine.b1 Fine.b2 = 3
markedT9Multiplicity Fine.b2 Fine.a0 = 3
markedT9Multiplicity Fine.b2 Fine.a1 = 3
markedT9Multiplicity Fine.b2 Fine.b0 = 3
markedT9Multiplicity Fine.b2 Fine.b1 = 3
markedT9Multiplicity Fine.b2 Fine.b2 = 1

markedT25Multiplicity : Fine.P11Fine5 → Fine.P11Fine5 → Nat
markedT25Multiplicity Fine.a0 Fine.a0 = 7
markedT25Multiplicity Fine.a0 Fine.a1 = 3
markedT25Multiplicity Fine.a0 Fine.b0 = 7
markedT25Multiplicity Fine.a0 Fine.b1 = 7
markedT25Multiplicity Fine.a0 Fine.b2 = 7
markedT25Multiplicity Fine.a1 Fine.a0 = 3
markedT25Multiplicity Fine.a1 Fine.a1 = 7
markedT25Multiplicity Fine.a1 Fine.b0 = 7
markedT25Multiplicity Fine.a1 Fine.b1 = 7
markedT25Multiplicity Fine.a1 Fine.b2 = 7
markedT25Multiplicity Fine.b0 Fine.a0 = 7
markedT25Multiplicity Fine.b0 Fine.a1 = 7
markedT25Multiplicity Fine.b0 Fine.b0 = 3
markedT25Multiplicity Fine.b0 Fine.b1 = 7
markedT25Multiplicity Fine.b0 Fine.b2 = 7
markedT25Multiplicity Fine.b1 Fine.a0 = 7
markedT25Multiplicity Fine.b1 Fine.a1 = 7
markedT25Multiplicity Fine.b1 Fine.b0 = 7
markedT25Multiplicity Fine.b1 Fine.b1 = 3
markedT25Multiplicity Fine.b1 Fine.b2 = 7
markedT25Multiplicity Fine.b2 Fine.a0 = 7
markedT25Multiplicity Fine.b2 Fine.a1 = 7
markedT25Multiplicity Fine.b2 Fine.b0 = 7
markedT25Multiplicity Fine.b2 Fine.b1 = 7
markedT25Multiplicity Fine.b2 Fine.b2 = 3

markedT3SquareEntry :
  (source target : Fine.P11Fine5) →
  pathCount Marked.MarkedT3Positive Marked.MarkedT3Positive source target
  ≡ markedT9Multiplicity source target + 3 * indicator target source
markedT3SquareEntry Fine.a0 Fine.a0 = refl
markedT3SquareEntry Fine.a0 Fine.a1 = refl
markedT3SquareEntry Fine.a0 Fine.b0 = refl
markedT3SquareEntry Fine.a0 Fine.b1 = refl
markedT3SquareEntry Fine.a0 Fine.b2 = refl
markedT3SquareEntry Fine.a1 Fine.a0 = refl
markedT3SquareEntry Fine.a1 Fine.a1 = refl
markedT3SquareEntry Fine.a1 Fine.b0 = refl
markedT3SquareEntry Fine.a1 Fine.b1 = refl
markedT3SquareEntry Fine.a1 Fine.b2 = refl
markedT3SquareEntry Fine.b0 Fine.a0 = refl
markedT3SquareEntry Fine.b0 Fine.a1 = refl
markedT3SquareEntry Fine.b0 Fine.b0 = refl
markedT3SquareEntry Fine.b0 Fine.b1 = refl
markedT3SquareEntry Fine.b0 Fine.b2 = refl
markedT3SquareEntry Fine.b1 Fine.a0 = refl
markedT3SquareEntry Fine.b1 Fine.a1 = refl
markedT3SquareEntry Fine.b1 Fine.b0 = refl
markedT3SquareEntry Fine.b1 Fine.b1 = refl
markedT3SquareEntry Fine.b1 Fine.b2 = refl
markedT3SquareEntry Fine.b2 Fine.a0 = refl
markedT3SquareEntry Fine.b2 Fine.a1 = refl
markedT3SquareEntry Fine.b2 Fine.b0 = refl
markedT3SquareEntry Fine.b2 Fine.b1 = refl
markedT3SquareEntry Fine.b2 Fine.b2 = refl

markedT5SquareEntry :
  (source target : Fine.P11Fine5) →
  pathCount Marked.MarkedT5Positive Marked.MarkedT5Positive source target
  ≡ markedT25Multiplicity source target + 5 * indicator target source
markedT5SquareEntry Fine.a0 Fine.a0 = refl
markedT5SquareEntry Fine.a0 Fine.a1 = refl
markedT5SquareEntry Fine.a0 Fine.b0 = refl
markedT5SquareEntry Fine.a0 Fine.b1 = refl
markedT5SquareEntry Fine.a0 Fine.b2 = refl
markedT5SquareEntry Fine.a1 Fine.a0 = refl
markedT5SquareEntry Fine.a1 Fine.a1 = refl
markedT5SquareEntry Fine.a1 Fine.b0 = refl
markedT5SquareEntry Fine.a1 Fine.b1 = refl
markedT5SquareEntry Fine.a1 Fine.b2 = refl
markedT5SquareEntry Fine.b0 Fine.a0 = refl
markedT5SquareEntry Fine.b0 Fine.a1 = refl
markedT5SquareEntry Fine.b0 Fine.b0 = refl
markedT5SquareEntry Fine.b0 Fine.b1 = refl
markedT5SquareEntry Fine.b0 Fine.b2 = refl
markedT5SquareEntry Fine.b1 Fine.a0 = refl
markedT5SquareEntry Fine.b1 Fine.a1 = refl
markedT5SquareEntry Fine.b1 Fine.b0 = refl
markedT5SquareEntry Fine.b1 Fine.b1 = refl
markedT5SquareEntry Fine.b1 Fine.b2 = refl
markedT5SquareEntry Fine.b2 Fine.a0 = refl
markedT5SquareEntry Fine.b2 Fine.a1 = refl
markedT5SquareEntry Fine.b2 Fine.b0 = refl
markedT5SquareEntry Fine.b2 Fine.b1 = refl
markedT5SquareEntry Fine.b2 Fine.b2 = refl

markedT9RowDegree : Nat
markedT9RowDegree = 13

markedT25RowDegree : Nat
markedT25RowDegree = 31

record P11MarkedX2HeckeAlgebraBoundary : Set where
  field
    correctedT3T5Commute : Bool
    correctedT3T5CommuteIsTrue : correctedT3T5Commute ≡ true

    correctedT3T5Symmetric : Bool
    correctedT3T5SymmetricIsTrue : correctedT3T5Symmetric ≡ true

    correctedT3PrimeSquareResidualPositive : Bool
    correctedT3PrimeSquareResidualPositiveIsTrue :
      correctedT3PrimeSquareResidualPositive ≡ true

    correctedT5PrimeSquareResidualPositive : Bool
    correctedT5PrimeSquareResidualPositiveIsTrue :
      correctedT5PrimeSquareResidualPositive ≡ true

    oldResidualMatricesReusedWithoutRecomputation : Bool
    oldResidualMatricesReusedWithoutRecomputationIsFalse :
      oldResidualMatricesReusedWithoutRecomputation ≡ false

canonicalP11MarkedX2HeckeAlgebraBoundary : P11MarkedX2HeckeAlgebraBoundary
canonicalP11MarkedX2HeckeAlgebraBoundary = record
  { correctedT3T5Commute = true
  ; correctedT3T5CommuteIsTrue = refl
  ; correctedT3T5Symmetric = true
  ; correctedT3T5SymmetricIsTrue = refl
  ; correctedT3PrimeSquareResidualPositive = true
  ; correctedT3PrimeSquareResidualPositiveIsTrue = refl
  ; correctedT5PrimeSquareResidualPositive = true
  ; correctedT5PrimeSquareResidualPositiveIsTrue = refl
  ; oldResidualMatricesReusedWithoutRecomputation = false
  ; oldResidualMatricesReusedWithoutRecomputationIsFalse = refl
  }
