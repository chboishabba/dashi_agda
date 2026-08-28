module DASHI.Foundations.BishopNatSquareRootDividedTangentExact where

------------------------------------------------------------------------
-- DIVIDED TANGENT INEQUALITY FOR POSITIVE NAT RADICAND
--
-- For 1<=n and r<=n, with A=sqrt(n), B=sqrt(n-r), the existing exact owner
-- proves
--
--   2AB + r <= 2A^2.
--
-- The newly-established positivity A>0 permits constructive cancellation by
-- 2A and yields
--
--   B + r/(2A) <= A.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_; _∸_)
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; _/_)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopNatSquareRootTangentExact as Tangent
import DASHI.Foundations.BishopNatSquareRootPositiveExact as RootPositive
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as Square
open import DASHI.Physics.YangMills.CompactLieProofLevel

rootNat : Nat → BishopReal.ℝ
rootNat = Tangent.rootNat

embedNat : Nat → BishopReal.ℝ
embedNat = Tangent.embedNat

two : BishopReal.ℝ
two = Tangent.two

twoPositive : BishopReal.Positive two
twoPositive =
  BishopP.0<x⇒posx
    (BishopP.p<q⇒p⋆<q⋆
      0ℚᵘ (+ 2 / 1)
      (ℚP.positive⁻¹ (+ 2 / 1)))

denominator : Nat → BishopReal.ℝ
denominator n = BishopReal._*_ two (rootNat n)

denominatorPositive :
  ∀ {n : Nat} → suc 0 ≤ n →
  BishopReal.Positive (denominator n)
denominatorPositive nPositive =
  BishopP.posx,y⇒posx*y
    twoPositive
    (RootPositive.canonicalFloorSquareRootPositive nPositive)

denominatorNonzero :
  ∀ {n : Nat} → suc 0 ≤ n →
  BishopReal._≄0 (denominator n)
denominatorNonzero nPositive =
  inj₂ (BishopP.posx⇒0<x (denominatorPositive nPositive))

inverseDenominator :
  (n : Nat) → suc 0 ≤ n → BishopReal.ℝ
inverseDenominator n nPositive =
  BishopInverse._⁻¹ (denominator n) (denominatorNonzero nPositive)

inverseDenominatorNonnegative :
  ∀ {n : Nat} (nPositive : suc 0 ≤ n) →
  BishopReal.NonNegative (inverseDenominator n nPositive)
inverseDenominatorNonnegative nPositive =
  BishopP.pos⇒nonNeg
    (BishopP.0<x⇒posx
      (BishopInverse.0<x⇒0<x⁻¹
        (denominatorNonzero nPositive)
        (BishopP.posx⇒0<x (denominatorPositive nPositive))))

crossAsDenominatorOrder :
  ∀ {n r : Nat} →
  r ≤ n →
  BishopReal._≤_
    (BishopReal._+_
      (BishopReal._*_ (denominator n) (rootNat (n ∸ r)))
      (embedNat r))
    (BishopReal._*_ (denominator n) (rootNat n))
crossAsDenominatorOrder {n} {r} r≤n =
  let
    raw = Tangent.bishopNatSquareRootTangentCrossMultiplied r≤n
    rightSquare :
      BishopReal._≃_
        (BishopReal._*_ Tangent.two (Tangent.embedNat n))
        (BishopReal._*_ (denominator n) (rootNat n))
    rightSquare =
      BishopP.≃-trans
        (BishopP.*-congˡ
          (BishopP.≃-symm
            (Square.canonicalFloorSquareRootSquaresToNat n)))
        (BishopP.*-assoc
          Tangent.two (rootNat n) (rootNat n))
    leftAssoc :
      BishopReal._≃_
        (BishopReal._+_
          (BishopReal._*_ Tangent.two
            (BishopReal._*_ (rootNat n) (rootNat (n ∸ r))))
          (embedNat r))
        (BishopReal._+_
          (BishopReal._*_ (denominator n) (rootNat (n ∸ r)))
          (embedNat r))
    leftAssoc =
      BishopP.+-congʳ
        (BishopP.*-assoc
          Tangent.two (rootNat n) (rootNat (n ∸ r)))
  in
  BishopP.≤-respʳ-≃ rightSquare
    (BishopP.≤-respˡ-≃ leftAssoc raw)

dividedTangentAdditive :
  ∀ {n r : Nat} →
  (nPositive : suc 0 ≤ n) →
  r ≤ n →
  BishopReal._≤_
    (BishopReal._+_
      (rootNat (n ∸ r))
      (BishopReal._*_
        (inverseDenominator n nPositive)
        (embedNat r)))
    (rootNat n)
dividedTangentAdditive {n} {r} nPositive r≤n =
  let
    inv = inverseDenominator n nPositive
    denom = denominator n
    raw = crossAsDenominatorOrder r≤n
    scaled =
      BishopP.*-monoˡ-≤-nonNeg
        raw
        (inverseDenominatorNonnegative nPositive)
    inverseLaw =
      BishopInverse.*-inverseˡ denom (denominatorNonzero nPositive)
    leftNormalize :
      BishopReal._≃_
        (BishopReal._*_ inv
          (BishopReal._+_
            (BishopReal._*_ denom (rootNat (n ∸ r)))
            (embedNat r)))
        (BishopReal._+_
          (rootNat (n ∸ r))
          (BishopReal._*_ inv (embedNat r)))
    leftNormalize =
      BishopP.≃-trans
        (BishopP.*-distribˡ-+
          inv
          (BishopReal._*_ denom (rootNat (n ∸ r)))
          (embedNat r))
        (BishopP.+-cong
          (BishopP.≃-trans
            (BishopP.≃-symm
              (BishopP.*-assoc inv denom (rootNat (n ∸ r))))
            (BishopP.≃-trans
              (BishopP.*-congʳ inverseLaw)
              (BishopP.*-identityˡ (rootNat (n ∸ r)))))
          BishopP.≃-refl)
    rightNormalize :
      BishopReal._≃_
        (BishopReal._*_ inv
          (BishopReal._*_ denom (rootNat n)))
        (rootNat n)
    rightNormalize =
      BishopP.≃-trans
        (BishopP.≃-symm
          (BishopP.*-assoc inv denom (rootNat n)))
        (BishopP.≃-trans
          (BishopP.*-congʳ inverseLaw)
          (BishopP.*-identityˡ (rootNat n)))
  in
  BishopP.≤-respʳ-≃ rightNormalize
    (BishopP.≤-respˡ-≃ leftNormalize scaled)

bishopNatSquareRootDividedTangentLevel : ProofLevel
bishopNatSquareRootDividedTangentLevel = machineChecked
