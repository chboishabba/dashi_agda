module DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact where

------------------------------------------------------------------------
-- ROUND179 / EXACT SAME-OUTPUT GRAM OBSTRUCTION
--
-- Round178 closes the pointwise estimate
--
--   ||K_a||^2 <= 9 |k|^2 E_a E_{k-a}.
--
-- This file answers the next question exactly: what is still missing when
-- several cells on the same output fibre are summed BEFORE absolute values?
--
-- For two C^3 cells u,v,
--
--   ||u+v||^2 = ||u||^2 + ||v||^2 + 2 Re<u,v>.
--
-- Hence a pointwise cell-mass bound alone cannot imply a cardinality-free
-- fibre bound: aligned cells have a positive Gram cross term.  Conversely,
-- once the signed network supplies a nonpositive/paid Gram cross term, the
-- cell masses add with no factor-of-two loss.
--
-- This isolates the exact Round179 frontier.  The next theorem must control
-- the signed SAME-OUTPUT GRAM CROSS TERM; another triangle/Cauchy pass over
-- cells would merely reintroduce convolution multiplicity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRawCurlLowOutputKernelMassRound178Exact as R178

F = R178.F

two : ℚ
two = 1ℚ + 1ℚ

twoNN : 0ℚ ≤ two
twoNN = Rational.addNonnegative R178.oneNN R178.oneNN

-- Real part of the Hermitian pairing, written directly in coordinates so the
-- polarization theorem is a literal polynomial identity over the rational
-- C^3 carrier.
realHermitianCross : C3.Complex3 F → C3.Complex3 F → ℚ
realHermitianCross
    (C3.complex3
      (C3.complex ax ayi) (C3.complex ay ayi2) (C3.complex az azi))
    (C3.complex3
      (C3.complex bx byi) (C3.complex by byi2) (C3.complex bz bzi)) =
  ax * bx + ayi * byi
  + ay * by + ayi2 * byi2
  + az * bz + azi * bzi

complex3Polarization :
  (u v : C3.Complex3 F) →
  L2.complex3NormSquared (C3.complex3Add u v)
  ≡ L2.complex3NormSquared u
    + L2.complex3NormSquared v
    + two * realHermitianCross u v
complex3Polarization
    (C3.complex3
      (C3.complex ax ayi) (C3.complex ay ayi2) (C3.complex az azi))
    (C3.complex3
      (C3.complex bx byi) (C3.complex by byi2) (C3.complex bz bzi)) =
  solve
    ( ax ∷ ayi ∷ ay ∷ ayi2 ∷ az ∷ azi
    ∷ bx ∷ byi ∷ by ∷ byi2 ∷ bz ∷ bzi ∷ [])

-- If the signed network makes the Gram cross term nonpositive, the two cell
-- masses add without any multiplicity loss.
nonpositiveGramRemovesTwoCellLoss :
  (u v : C3.Complex3 F) →
  realHermitianCross u v ≤ 0ℚ →
  L2.complex3NormSquared (C3.complex3Add u v)
  ≤ L2.complex3NormSquared u + L2.complex3NormSquared v
nonpositiveGramRemovesTwoCellLoss u v crossNonpositive =
  let
    scaled : two * realHermitianCross u v ≤ two * 0ℚ
    scaled =
      let instance twoNNI = nonNegative twoNN
      in ℚP.*-monoˡ-≤-nonNeg two crossNonpositive

    added :
      L2.complex3NormSquared u + L2.complex3NormSquared v
        + two * realHermitianCross u v
      ≤
      L2.complex3NormSquared u + L2.complex3NormSquared v
        + two * 0ℚ
    added = ℚP.+-monoʳ-≤
      (L2.complex3NormSquared u + L2.complex3NormSquared v)
      scaled

    rhsZero :
      L2.complex3NormSquared u + L2.complex3NormSquared v + two * 0ℚ
      ≡ L2.complex3NormSquared u + L2.complex3NormSquared v
    rhsZero = solve
      (L2.complex3NormSquared u ∷ L2.complex3NormSquared v ∷ [])
  in
  subst
    (λ left → left ≤ L2.complex3NormSquared u + L2.complex3NormSquared v)
    (complex3Polarization u v)
    (subst
      (L2.complex3NormSquared u + L2.complex3NormSquared v
        + two * realHermitianCross u v ≤_)
      rhsZero
      added)

-- Exact aligned witness: two individually unit-mass cells have total squared
-- mass four.  Thus the local mass theorem by itself cannot be summed with
-- coefficient one; the missing datum really is the signed Gram cross term.
alignedCell : C3.Complex3 F
alignedCell = C3.complex3
  (C3.complex 1ℚ 0ℚ)
  (C3.complex 0ℚ 0ℚ)
  (C3.complex 0ℚ 0ℚ)

alignedCellMassIsOne : L2.complex3NormSquared alignedCell ≡ 1ℚ
alignedCellMassIsOne = solve []

alignedPairMassIsFour :
  L2.complex3NormSquared (C3.complex3Add alignedCell alignedCell)
  ≡ two * (two * 1ℚ)
alignedPairMassIsFour = solve []

alignedIndividualMassSumIsTwo :
  L2.complex3NormSquared alignedCell + L2.complex3NormSquared alignedCell
  ≡ two * 1ℚ
alignedIndividualMassSumIsTwo = solve []

alignedGramCrossIsOne : realHermitianCross alignedCell alignedCell ≡ 1ℚ
alignedGramCrossIsOne = solve []

round179PolarizationClosed : Bool
round179PolarizationClosed = true

round179PointwiseMassAloneClosesFibre : Bool
round179PointwiseMassAloneClosesFibre = false

round179SignedGramCrossTermIsNextOwner : Bool
round179SignedGramCrossTermIsNextOwner = true

round179PackageAClosed : Bool
round179PackageAClosed = false

round179ClayPromotion : Bool
round179ClayPromotion = false
