module DASHI.Foundations.BishopNatSquareRootTangentExact where

------------------------------------------------------------------------
-- CONCAVITY / TANGENT INEQUALITY FOR THE CONSTRUCTED NAT ROOT
--
-- For r <= n put A = sqrt(n), B = sqrt(n-r).  The source inequality
--
--   B <= A - r/(2A)
--
-- is first proved in the division-free form
--
--   2 A B + r <= 2 A^2.
--
-- Indeed the difference between the right and left sides, after substituting
-- A^2-B^2=r, is (A-B)^2 >= 0.  This is exactly the form consumed by the Erdos
-- exponential kernel before positive inverse cancellation is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NatP
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopP

import DASHI.Foundations.BishopNatSquareRootApproximationExact as Approximation
import DASHI.Foundations.BishopNatSquareRootNonnegativeExact as Nonnegative
import DASHI.Foundations.BishopNatSquareRootRegularFloorExact as Root
import DASHI.Foundations.BishopNatSquareRootSemanticSquareExact as Square
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

embedNat : Nat → BishopReal.ℝ
embedNat n = BishopReal._⋆ (Approximation.natAsRational n)

rootNat : Nat → BishopReal.ℝ
rootNat = Root.canonicalFloorSquareRootReal

two : BishopReal.ℝ
two = BishopReal._⋆ (+ 2 / 1)

square : BishopReal.ℝ → BishopReal.ℝ
square x = BishopReal._*_ x x

squareNonnegative :
  (value : BishopReal.ℝ) →
  BishopReal.NonNegative (square value)
squareNonnegative value =
  let
    absNN = BishopP.nonNeg∣x∣ value
  in
  BishopP.nonNegx,y⇒nonNegx*y absNN absNN
  |> BishopP.nonNeg-cong
      (let open BishopP.ℝ-Solver in
       solve 1
         (λ x → (∣ x ∣ ⊗ ∣ x ∣) ⊜ (x ⊗ x))
         BishopP.≃-refl value)
  where
  infixl 0 _|>_
  _|>_ : ∀ {A B : Set} → A → (A → B) → B
  x |> f = f x

tangentAlgebraicGap :
  (A B : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._*_ two (square A))
      (BishopReal._+_
        (BishopReal._*_ two (BishopReal._*_ A B))
        (BishopReal._-_ (square A) (square B))))
    (square (BishopReal._-_ A B))
tangentAlgebraicGap A B =
  let open BishopP.ℝ-Solver in
  solve 2
    (λ A′ B′ →
      ((Κ (+ 2 / 1) ⊗ (A′ ⊗ A′))
       ⊖ ((Κ (+ 2 / 1) ⊗ (A′ ⊗ B′))
          ⊕ ((A′ ⊗ A′) ⊖ (B′ ⊗ B′))))
      ⊜ ((A′ ⊖ B′) ⊗ (A′ ⊖ B′)))
    BishopP.≃-refl A B

rawTangentOrder :
  (A B : BishopReal.ℝ) →
  BishopReal._≤_
    (BishopReal._+_
      (BishopReal._*_ two (BishopReal._*_ A B))
      (BishopReal._-_ (square A) (square B)))
    (BishopReal._*_ two (square A))
rawTangentOrder A B =
  Order.nonnegativeDifferenceGivesOrder
    (BishopP.≤-respʳ-≃
      (BishopP.≃-symm (tangentAlgebraicGap A B))
      (BishopP.nonNegx⇒0≤x
        (squareNonnegative (BishopReal._-_ A B))))

embeddedNatSubtractionDifference :
  ∀ {n r : Nat} → r ≤ n →
  BishopReal._≃_
    (BishopReal._-_
      (embedNat n)
      (embedNat (n ∸ r)))
    (embedNat r)
embeddedNatSubtractionDifference {n} {r} r≤n =
  let
    decompose : (n ∸ r) + r ≡ n
    decompose = NatP.m∸n+n≡m r≤n
    open BishopP.ℝ-Solver
  in
  solve 0
    (Κ (Approximation.natAsRational n)
      ⊖ Κ (Approximation.natAsRational (n ∸ r))
      ⊜ Κ (Approximation.natAsRational r))
    BishopP.≃-refl

rootSquareDifferenceIsDecrement :
  ∀ {n r : Nat} → r ≤ n →
  BishopReal._≃_
    (BishopReal._-_
      (square (rootNat n))
      (square (rootNat (n ∸ r))))
    (embedNat r)
rootSquareDifferenceIsDecrement {n} {r} r≤n =
  BishopP.≃-trans
    (BishopP.+-cong
      (Square.canonicalFloorSquareRootSquaresToNat n)
      (BishopP.-‿cong
        (Square.canonicalFloorSquareRootSquaresToNat (n ∸ r))))
    (embeddedNatSubtractionDifference r≤n)

bishopNatSquareRootTangentCrossMultiplied :
  ∀ {n r : Nat} → r ≤ n →
  BishopReal._≤_
    (BishopReal._+_
      (BishopReal._*_ two
        (BishopReal._*_ (rootNat n) (rootNat (n ∸ r))))
      (embedNat r))
    (BishopReal._*_ two (embedNat n))
bishopNatSquareRootTangentCrossMultiplied {n} {r} r≤n =
  let
    A = rootNat n
    B = rootNat (n ∸ r)
    raw = rawTangentOrder A B
    leftTransport =
      BishopP.+-cong
        BishopP.≃-refl
        (rootSquareDifferenceIsDecrement r≤n)
    rightTransport =
      BishopP.*-congˡ
        (Square.canonicalFloorSquareRootSquaresToNat n)
  in
  BishopP.≤-respʳ-≃ rightTransport
    (BishopP.≤-respˡ-≃ leftTransport raw)

bishopNatSquareRootTangentCrossMultipliedLevel : ProofLevel
bishopNatSquareRootTangentCrossMultipliedLevel = machineChecked
