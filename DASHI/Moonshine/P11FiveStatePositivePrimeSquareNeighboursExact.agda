module DASHI.Moonshine.P11FiveStatePositivePrimeSquareNeighboursExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- Upgrade the entrywise-positive prime-square residuals of the five-state
-- candidate into literal finite neighbour systems.
--
-- The residual row sums are
--
--   R4  :  7,
--   R9  : 13,
--   R25 : 31,
--
-- matching sigma_1(4), sigma_1(9), sigma_1(25) on the constant line.  Each row
-- below is built from repeated actual target vertices, so positivity is present
-- before linearization.  Indicator counts recover exactly the residual matrices
-- already proved in P11FiveStatePositiveHeckeAlgebraExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Fin using (Fin)
open import Data.Vec.Base using (Vec; replicate; lookup; _++_)

import DASHI.Moonshine.PositiveFiniteNeighbourSystemExact as Positive
import DASHI.Moonshine.P11FiveStatePositiveHeckeLiftExact as Fine
import DASHI.Moonshine.P11FiveStatePositiveHeckeAlgebraExact as Algebra

------------------------------------------------------------------------
-- R4 rows, arity 7.
------------------------------------------------------------------------

r4Row : Fine.P11Fine5 → Vec Fine.P11Fine5 7
r4Row Fine.a0 =
  replicate 1 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 1 Fine.b0 ++ replicate 1 Fine.b1 ++ replicate 1 Fine.b2
r4Row Fine.a1 =
  replicate 3 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 1 Fine.b0 ++ replicate 1 Fine.b1 ++ replicate 1 Fine.b2
r4Row Fine.b0 =
  replicate 1 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 1 Fine.b0 ++ replicate 2 Fine.b1 ++ replicate 2 Fine.b2
r4Row Fine.b1 =
  replicate 1 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 2 Fine.b0 ++ replicate 1 Fine.b1 ++ replicate 2 Fine.b2
r4Row Fine.b2 =
  replicate 1 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 2 Fine.b0 ++ replicate 2 Fine.b1 ++ replicate 1 Fine.b2

R4Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
R4Positive =
  record
    { Positive.arity = 7
    ; Positive.neighbour = λ source edge → lookup (r4Row source) edge
    }

------------------------------------------------------------------------
-- R9 rows, arity 13: one self and three copies of every other vertex.
------------------------------------------------------------------------

r9Row : Fine.P11Fine5 → Vec Fine.P11Fine5 13
r9Row Fine.a0 =
  replicate 1 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
r9Row Fine.a1 =
  replicate 3 Fine.a0 ++ replicate 1 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
r9Row Fine.b0 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 1 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 3 Fine.b2
r9Row Fine.b1 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 1 Fine.b1 ++ replicate 3 Fine.b2
r9Row Fine.b2 =
  replicate 3 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 3 Fine.b0 ++ replicate 3 Fine.b1 ++ replicate 1 Fine.b2

R9Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
R9Positive =
  record
    { Positive.arity = 13
    ; Positive.neighbour = λ source edge → lookup (r9Row source) edge
    }

------------------------------------------------------------------------
-- R25 rows, arity 31.
------------------------------------------------------------------------

r25Row : Fine.P11Fine5 → Vec Fine.P11Fine5 31
r25Row Fine.a0 =
  replicate 7 Fine.a0 ++ replicate 3 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 7 Fine.b2
r25Row Fine.a1 =
  replicate 3 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 7 Fine.b0 ++ replicate 7 Fine.b1 ++ replicate 7 Fine.b2
r25Row Fine.b0 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 5 Fine.b0 ++ replicate 6 Fine.b1 ++ replicate 6 Fine.b2
r25Row Fine.b1 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 6 Fine.b0 ++ replicate 5 Fine.b1 ++ replicate 6 Fine.b2
r25Row Fine.b2 =
  replicate 7 Fine.a0 ++ replicate 7 Fine.a1 ++
  replicate 6 Fine.b0 ++ replicate 6 Fine.b1 ++ replicate 5 Fine.b2

R25Positive : Positive.PositiveFiniteNeighbourSystem Fine.P11Fine5
R25Positive =
  record
    { Positive.arity = 31
    ; Positive.neighbour = λ source edge → lookup (r25Row source) edge
    }

------------------------------------------------------------------------
-- The literal neighbour counts recover the residual multiplicity functions.
------------------------------------------------------------------------

r4CountExact :
  (source target : Fine.P11Fine5) →
  Positive.positiveOperator R4Positive (Algebra.indicator target) source
  ≡ Algebra.r4Multiplicity source target
r4CountExact Fine.a0 Fine.a0 = refl
r4CountExact Fine.a0 Fine.a1 = refl
r4CountExact Fine.a0 Fine.b0 = refl
r4CountExact Fine.a0 Fine.b1 = refl
r4CountExact Fine.a0 Fine.b2 = refl
r4CountExact Fine.a1 Fine.a0 = refl
r4CountExact Fine.a1 Fine.a1 = refl
r4CountExact Fine.a1 Fine.b0 = refl
r4CountExact Fine.a1 Fine.b1 = refl
r4CountExact Fine.a1 Fine.b2 = refl
r4CountExact Fine.b0 Fine.a0 = refl
r4CountExact Fine.b0 Fine.a1 = refl
r4CountExact Fine.b0 Fine.b0 = refl
r4CountExact Fine.b0 Fine.b1 = refl
r4CountExact Fine.b0 Fine.b2 = refl
r4CountExact Fine.b1 Fine.a0 = refl
r4CountExact Fine.b1 Fine.a1 = refl
r4CountExact Fine.b1 Fine.b0 = refl
r4CountExact Fine.b1 Fine.b1 = refl
r4CountExact Fine.b1 Fine.b2 = refl
r4CountExact Fine.b2 Fine.a0 = refl
r4CountExact Fine.b2 Fine.a1 = refl
r4CountExact Fine.b2 Fine.b0 = refl
r4CountExact Fine.b2 Fine.b1 = refl
r4CountExact Fine.b2 Fine.b2 = refl

r9CountExact :
  (source target : Fine.P11Fine5) →
  Positive.positiveOperator R9Positive (Algebra.indicator target) source
  ≡ Algebra.r9Multiplicity source target
r9CountExact Fine.a0 Fine.a0 = refl
r9CountExact Fine.a0 Fine.a1 = refl
r9CountExact Fine.a0 Fine.b0 = refl
r9CountExact Fine.a0 Fine.b1 = refl
r9CountExact Fine.a0 Fine.b2 = refl
r9CountExact Fine.a1 Fine.a0 = refl
r9CountExact Fine.a1 Fine.a1 = refl
r9CountExact Fine.a1 Fine.b0 = refl
r9CountExact Fine.a1 Fine.b1 = refl
r9CountExact Fine.a1 Fine.b2 = refl
r9CountExact Fine.b0 Fine.a0 = refl
r9CountExact Fine.b0 Fine.a1 = refl
r9CountExact Fine.b0 Fine.b0 = refl
r9CountExact Fine.b0 Fine.b1 = refl
r9CountExact Fine.b0 Fine.b2 = refl
r9CountExact Fine.b1 Fine.a0 = refl
r9CountExact Fine.b1 Fine.a1 = refl
r9CountExact Fine.b1 Fine.b0 = refl
r9CountExact Fine.b1 Fine.b1 = refl
r9CountExact Fine.b1 Fine.b2 = refl
r9CountExact Fine.b2 Fine.a0 = refl
r9CountExact Fine.b2 Fine.a1 = refl
r9CountExact Fine.b2 Fine.b0 = refl
r9CountExact Fine.b2 Fine.b1 = refl
r9CountExact Fine.b2 Fine.b2 = refl

r25CountExact :
  (source target : Fine.P11Fine5) →
  Positive.positiveOperator R25Positive (Algebra.indicator target) source
  ≡ Algebra.r25Multiplicity source target
r25CountExact Fine.a0 Fine.a0 = refl
r25CountExact Fine.a0 Fine.a1 = refl
r25CountExact Fine.a0 Fine.b0 = refl
r25CountExact Fine.a0 Fine.b1 = refl
r25CountExact Fine.a0 Fine.b2 = refl
r25CountExact Fine.a1 Fine.a0 = refl
r25CountExact Fine.a1 Fine.a1 = refl
r25CountExact Fine.a1 Fine.b0 = refl
r25CountExact Fine.a1 Fine.b1 = refl
r25CountExact Fine.a1 Fine.b2 = refl
r25CountExact Fine.b0 Fine.a0 = refl
r25CountExact Fine.b0 Fine.a1 = refl
r25CountExact Fine.b0 Fine.b0 = refl
r25CountExact Fine.b0 Fine.b1 = refl
r25CountExact Fine.b0 Fine.b2 = refl
r25CountExact Fine.b1 Fine.a0 = refl
r25CountExact Fine.b1 Fine.a1 = refl
r25CountExact Fine.b1 Fine.b0 = refl
r25CountExact Fine.b1 Fine.b1 = refl
r25CountExact Fine.b1 Fine.b2 = refl
r25CountExact Fine.b2 Fine.a0 = refl
r25CountExact Fine.b2 Fine.a1 = refl
r25CountExact Fine.b2 Fine.b0 = refl
r25CountExact Fine.b2 Fine.b1 = refl
r25CountExact Fine.b2 Fine.b2 = refl

------------------------------------------------------------------------
-- Prime-square Hecke relations are now equalities between positive path counts
-- and positive neighbour counts plus the true fine identity, entry by entry.
------------------------------------------------------------------------

r2SquarePositiveEntry :
  (source target : Fine.P11Fine5) →
  Algebra.pathCount Fine.R2Positive Fine.R2Positive source target
  ≡ Positive.positiveOperator R4Positive (Algebra.indicator target) source
      + 2 * Algebra.indicator target source
r2SquarePositiveEntry source target =
  trans
    (Algebra.r2SquareEntry source target)
    (cong (λ value → value + 2 * Algebra.indicator target source)
      (sym (r4CountExact source target)))

r3SquarePositiveEntry :
  (source target : Fine.P11Fine5) →
  Algebra.pathCount Fine.R3Positive Fine.R3Positive source target
  ≡ Positive.positiveOperator R9Positive (Algebra.indicator target) source
      + 3 * Algebra.indicator target source
r3SquarePositiveEntry source target =
  trans
    (Algebra.r3SquareEntry source target)
    (cong (λ value → value + 3 * Algebra.indicator target source)
      (sym (r9CountExact source target)))

r5SquarePositiveEntry :
  (source target : Fine.P11Fine5) →
  Algebra.pathCount Fine.R5Positive Fine.R5Positive source target
  ≡ Positive.positiveOperator R25Positive (Algebra.indicator target) source
      + 5 * Algebra.indicator target source
r5SquarePositiveEntry source target =
  trans
    (Algebra.r5SquareEntry source target)
    (cong (λ value → value + 5 * Algebra.indicator target source)
      (sym (r25CountExact source target)))

record P11FiveStatePositivePrimeSquareBoundary : Set where
  field
    r4PositiveNeighbourSystemConstructed : Bool
    r4PositiveNeighbourSystemConstructedIsTrue :
      r4PositiveNeighbourSystemConstructed ≡ true

    r9PositiveNeighbourSystemConstructed : Bool
    r9PositiveNeighbourSystemConstructedIsTrue :
      r9PositiveNeighbourSystemConstructed ≡ true

    r25PositiveNeighbourSystemConstructed : Bool
    r25PositiveNeighbourSystemConstructedIsTrue :
      r25PositiveNeighbourSystemConstructed ≡ true

    allPrimeSquareRelationsUseTrueFineIdentity : Bool
    allPrimeSquareRelationsUseTrueFineIdentityIsTrue :
      allPrimeSquareRelationsUseTrueFineIdentity ≡ true

    allPrimeSquareResidualsPositiveBeforeLinearization : Bool
    allPrimeSquareResidualsPositiveBeforeLinearizationIsTrue :
      allPrimeSquareResidualsPositiveBeforeLinearization ≡ true

    quaternionIdealClassInterpretationConstructedHere : Bool
    quaternionIdealClassInterpretationConstructedHereIsFalse :
      quaternionIdealClassInterpretationConstructedHere ≡ false

canonicalP11FiveStatePositivePrimeSquareBoundary :
  P11FiveStatePositivePrimeSquareBoundary
canonicalP11FiveStatePositivePrimeSquareBoundary =
  record
    { r4PositiveNeighbourSystemConstructed = true
    ; r4PositiveNeighbourSystemConstructedIsTrue = refl
    ; r9PositiveNeighbourSystemConstructed = true
    ; r9PositiveNeighbourSystemConstructedIsTrue = refl
    ; r25PositiveNeighbourSystemConstructed = true
    ; r25PositiveNeighbourSystemConstructedIsTrue = refl
    ; allPrimeSquareRelationsUseTrueFineIdentity = true
    ; allPrimeSquareRelationsUseTrueFineIdentityIsTrue = refl
    ; allPrimeSquareResidualsPositiveBeforeLinearization = true
    ; allPrimeSquareResidualsPositiveBeforeLinearizationIsTrue = refl
    ; quaternionIdealClassInterpretationConstructedHere = false
    ; quaternionIdealClassInterpretationConstructedHereIsFalse = refl
    }
