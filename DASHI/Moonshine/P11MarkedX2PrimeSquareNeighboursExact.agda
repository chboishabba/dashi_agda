module DASHI.Moonshine.P11MarkedX2PrimeSquareNeighboursExact where

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
-- DASHI CONTRIBUTION
--
-- Turn the recomputed marked prime-square residuals into literal positive
-- neighbour systems.  This is the true-identity test requested after the
-- quaternion correction of T3 and T5.
--
-- The corrected marked relations are
--
--   (T3^X(2))^2 = T9^X(2)  + 3 I,
--   (T5^X(2))^2 = T25^X(2) + 5 I,
--
-- with T9 and T25 positive before linearization and row degrees 13 and 31.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec.Base using (Vec; replicate; lookup; _++_)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11MarkedX2HeckeReconstructionExact as Marked
import DASHI.Moonshine.P11MarkedX2HeckeAlgebraExact as Algebra

------------------------------------------------------------------------
-- Corrected T9 rows.
------------------------------------------------------------------------

markedT9Row : Fine.P11Fine5 → Vec Fine.P11Fine5 13
markedT9Row Fine.a0 =
  replicate 1 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
markedT9Row Fine.a1 =
  replicate 3 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
markedT9Row Fine.b0 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 1 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
markedT9Row Fine.b1 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 1 Fine.b1 ++ replicate 3 Fine.b2
markedT9Row Fine.b2 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 1 Fine.b2

MarkedT9Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
MarkedT9Positive = record
  { Positive.arity = 13
  ; Positive.neighbour = λ source edge → lookup (markedT9Row source) edge
  }

------------------------------------------------------------------------
-- Corrected T25 rows.
------------------------------------------------------------------------

markedT25Row : Fine.P11Fine5 → Vec Fine.P11Fine5 31
markedT25Row Fine.a0 =
  replicate 7 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 7 Fine.b2
markedT25Row Fine.a1 =
  replicate 3 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 7 Fine.b2
markedT25Row Fine.b0 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 7 Fine.b2
markedT25Row Fine.b1 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 7 Fine.b2
markedT25Row Fine.b2 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 3 Fine.b2

MarkedT25Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
MarkedT25Positive = record
  { Positive.arity = 31
  ; Positive.neighbour = λ source edge → lookup (markedT25Row source) edge
  }

------------------------------------------------------------------------
-- Literal counts equal the residual functions.
------------------------------------------------------------------------

markedT9CountExact :
  (source target : Fine.P11Fine5) →
  Positive.positiveOperator MarkedT9Positive (Algebra.indicator target) source
  ≡ Algebra.markedT9Multiplicity source target
markedT9CountExact Fine.a0 Fine.a0 = refl
markedT9CountExact Fine.a0 Fine.a1 = refl
markedT9CountExact Fine.a0 Fine.b0 = refl
markedT9CountExact Fine.a0 Fine.b1 = refl
markedT9CountExact Fine.a0 Fine.b2 = refl
markedT9CountExact Fine.a1 Fine.a0 = refl
markedT9CountExact Fine.a1 Fine.a1 = refl
markedT9CountExact Fine.a1 Fine.b0 = refl
markedT9CountExact Fine.a1 Fine.b1 = refl
markedT9CountExact Fine.a1 Fine.b2 = refl
markedT9CountExact Fine.b0 Fine.a0 = refl
markedT9CountExact Fine.b0 Fine.a1 = refl
markedT9CountExact Fine.b0 Fine.b0 = refl
markedT9CountExact Fine.b0 Fine.b1 = refl
markedT9CountExact Fine.b0 Fine.b2 = refl
markedT9CountExact Fine.b1 Fine.a0 = refl
markedT9CountExact Fine.b1 Fine.a1 = refl
markedT9CountExact Fine.b1 Fine.b0 = refl
markedT9CountExact Fine.b1 Fine.b1 = refl
markedT9CountExact Fine.b1 Fine.b2 = refl
markedT9CountExact Fine.b2 Fine.a0 = refl
markedT9CountExact Fine.b2 Fine.a1 = refl
markedT9CountExact Fine.b2 Fine.b0 = refl
markedT9CountExact Fine.b2 Fine.b1 = refl
markedT9CountExact Fine.b2 Fine.b2 = refl

markedT25CountExact :
  (source target : Fine.P11Fine5) →
  Positive.positiveOperator MarkedT25Positive (Algebra.indicator target) source
  ≡ Algebra.markedT25Multiplicity source target
markedT25CountExact Fine.a0 Fine.a0 = refl
markedT25CountExact Fine.a0 Fine.a1 = refl
markedT25CountExact Fine.a0 Fine.b0 = refl
markedT25CountExact Fine.a0 Fine.b1 = refl
markedT25CountExact Fine.a0 Fine.b2 = refl
markedT25CountExact Fine.a1 Fine.a0 = refl
markedT25CountExact Fine.a1 Fine.a1 = refl
markedT25CountExact Fine.a1 Fine.b0 = refl
markedT25CountExact Fine.a1 Fine.b1 = refl
markedT25CountExact Fine.a1 Fine.b2 = refl
markedT25CountExact Fine.b0 Fine.a0 = refl
markedT25CountExact Fine.b0 Fine.a1 = refl
markedT25CountExact Fine.b0 Fine.b0 = refl
markedT25CountExact Fine.b0 Fine.b1 = refl
markedT25CountExact Fine.b0 Fine.b2 = refl
markedT25CountExact Fine.b1 Fine.a0 = refl
markedT25CountExact Fine.b1 Fine.a1 = refl
markedT25CountExact Fine.b1 Fine.b0 = refl
markedT25CountExact Fine.b1 Fine.b1 = refl
markedT25CountExact Fine.b1 Fine.b2 = refl
markedT25CountExact Fine.b2 Fine.a0 = refl
markedT25CountExact Fine.b2 Fine.a1 = refl
markedT25CountExact Fine.b2 Fine.b0 = refl
markedT25CountExact Fine.b2 Fine.b1 = refl
markedT25CountExact Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- True-identity prime-square relations at the positive neighbour level.
------------------------------------------------------------------------

markedT3SquarePositiveEntry :
  (source target : Fine.P11Fine5) →
  Algebra.pathCount Marked.MarkedT3Positive Marked.MarkedT3Positive source target
  ≡ Positive.positiveOperator MarkedT9Positive (Algebra.indicator target) source
      + 3 * Algebra.indicator target source
markedT3SquarePositiveEntry source target =
  trans
    (Algebra.markedT3SquareEntry source target)
    (cong (λ value → value + 3 * Algebra.indicator target source)
      (sym (markedT9CountExact source target)))

markedT5SquarePositiveEntry :
  (source target : Fine.P11Fine5) →
  Algebra.pathCount Marked.MarkedT5Positive Marked.MarkedT5Positive source target
  ≡ Positive.positiveOperator MarkedT25Positive (Algebra.indicator target) source
      + 5 * Algebra.indicator target source
markedT5SquarePositiveEntry source target =
  trans
    (Algebra.markedT5SquareEntry source target)
    (cong (λ value → value + 5 * Algebra.indicator target source)
      (sym (markedT25CountExact source target)))

record P11MarkedX2PrimeSquareBoundary : Set where
  field
    correctedT9PositiveConstructed : Bool
    correctedT9PositiveConstructedIsTrue : correctedT9PositiveConstructed ≡ true

    correctedT25PositiveConstructed : Bool
    correctedT25PositiveConstructedIsTrue : correctedT25PositiveConstructed ≡ true

    correctedT3SquareUsesTrueIdentity : Bool
    correctedT3SquareUsesTrueIdentityIsTrue : correctedT3SquareUsesTrueIdentity ≡ true

    correctedT5SquareUsesTrueIdentity : Bool
    correctedT5SquareUsesTrueIdentityIsTrue : correctedT5SquareUsesTrueIdentity ≡ true

canonicalP11MarkedX2PrimeSquareBoundary : P11MarkedX2PrimeSquareBoundary
canonicalP11MarkedX2PrimeSquareBoundary = record
  { correctedT9PositiveConstructed = true
  ; correctedT9PositiveConstructedIsTrue = refl
  ; correctedT25PositiveConstructed = true
  ; correctedT25PositiveConstructedIsTrue = refl
  ; correctedT3SquareUsesTrueIdentity = true
  ; correctedT3SquareUsesTrueIdentityIsTrue = refl
  ; correctedT5SquareUsesTrueIdentity = true
  ; correctedT5SquareUsesTrueIdentityIsTrue = refl
  }
