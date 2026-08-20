module DASHI.Moonshine.P37MarkedX2FrobeniusFrickeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Adel Betina and Emmanuel Lecouturier,
-- "Congruence formulae for Legendre modular polynomials",
-- Journal of Number Theory 188 (2018), 71--87.
-- DOI: 10.1016/j.jnt.2018.01.006.
-- They describe X(Gamma_0(p) intersection Gamma(2)) in characteristic p and
-- identify the Atkin--Lehner gluing on the supersingular special fibre through
-- Frobenius on the Legendre/full-level-2 coordinate.
--
-- Josep Gonzalez,
-- "On the p-th division polynomial", Journal of Number Theory 233 (2022),
-- 285--300. DOI: 10.1016/j.jnt.2021.06.011.
-- Deuring/Legendre supersingular polynomial context.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Reuse the independently constructed p=37 full-level-2 Deuring carrier.
-- Its 18 points are nine irreducible quadratic pairs, so marked Frobenius swaps
-- every pair and has no fixed point.  Betina--Lecouturier supplies the same
-- special-fibre Atkin--Lehner/Frobenius identification used at p=11; hence the
-- marked Fricke fingerprint is exactly this involution.
--
-- This constructs the p=37 marked Frobenius/Fricke action itself.  It does not
-- claim marked T3/T5 equivariance before the corresponding p=37 marked Hecke
-- correspondences have been constructed.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P37NonOggFullLevel2DeuringControlExact as P37

markedFrobenius37 : P37.P37SupersingularLambda → P37.P37SupersingularLambda
markedFrobenius37 = P37.p37MarkedFrobenius

markedFrobenius37Involution :
  (x : P37.P37SupersingularLambda) →
  markedFrobenius37 (markedFrobenius37 x) ≡ x
markedFrobenius37Involution = P37.p37MarkedFrobeniusInvolution

markedFrobenius37NoFixedPoint :
  (x : P37.P37SupersingularLambda) →
  markedFrobenius37 x ≡ x → ⊥
markedFrobenius37NoFixedPoint = P37.p37MarkedFrobeniusHasNoFixedPoint

markedFricke37 : P37.P37SupersingularLambda → P37.P37SupersingularLambda
markedFricke37 = markedFrobenius37

markedFricke37Involution :
  (x : P37.P37SupersingularLambda) →
  markedFricke37 (markedFricke37 x) ≡ x
markedFricke37Involution = markedFrobenius37Involution

markedFricke37NoFixedPoint :
  (x : P37.P37SupersingularLambda) → markedFricke37 x ≡ x → ⊥
markedFricke37NoFixedPoint = markedFrobenius37NoFixedPoint

markedFricke37PairCount : Nat
markedFricke37PairCount = P37.p37MarkedFrobeniusPairCount

markedFricke37PairCountIsNine : markedFricke37PairCount ≡ 9
markedFricke37PairCountIsNine = refl

markedFricke37FixedCount : Nat
markedFricke37FixedCount = 0

markedFricke37FixedCountIsZero : markedFricke37FixedCount ≡ 0
markedFricke37FixedCountIsZero = refl

record P37MarkedX2FrobeniusFrickeBoundary : Set where
  field
    markedGeometricFrobeniusConsumed : Bool
    markedGeometricFrobeniusConsumedIsTrue :
      markedGeometricFrobeniusConsumed ≡ true

    markedFrickeSpecialFiberActionConstructed : Bool
    markedFrickeSpecialFiberActionConstructedIsTrue :
      markedFrickeSpecialFiberActionConstructed ≡ true

    ninePairsZeroFixedConstructed : Bool
    ninePairsZeroFixedConstructedIsTrue : ninePairsZeroFixedConstructed ≡ true

    markedT3T5FrickeEquivarianceClaimedHere : Bool
    markedT3T5FrickeEquivarianceClaimedHereIsFalse :
      markedT3T5FrickeEquivarianceClaimedHere ≡ false

canonicalP37MarkedX2FrobeniusFrickeBoundary :
  P37MarkedX2FrobeniusFrickeBoundary
canonicalP37MarkedX2FrobeniusFrickeBoundary = record
  { markedGeometricFrobeniusConsumed = true
  ; markedGeometricFrobeniusConsumedIsTrue = refl
  ; markedFrickeSpecialFiberActionConstructed = true
  ; markedFrickeSpecialFiberActionConstructedIsTrue = refl
  ; ninePairsZeroFixedConstructed = true
  ; ninePairsZeroFixedConstructedIsTrue = refl
  ; markedT3T5FrickeEquivarianceClaimedHere = false
  ; markedT3T5FrickeEquivarianceClaimedHereIsFalse = refl
  }
