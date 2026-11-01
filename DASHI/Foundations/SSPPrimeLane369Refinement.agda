module DASHI.Foundations.SSPPrimeLane369Refinement where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.TrackedPrimes using (SSP; p3)

------------------------------------------------------------------------
-- Depth-indexed 3/6/9 refinement carrier for a single tracked SSP lane.
--
-- The carrier is intentionally finite and structural:
--   * a three-way digit set for local 3/6/9 refinement,
--   * a recursive address tree indexed by depth,
--   * prefix extraction by one-step truncation,
--   * a lane-level wrapper that keeps the prime lane explicit.

three : Nat
three = suc (suc (suc zero))

six : Nat
six = suc (suc (suc three))

nine : Nat
nine = suc (suc (suc six))

data Lane369Digit : Set where
  digit-3 : Lane369Digit
  digit-6 : Lane369Digit
  digit-9 : Lane369Digit

digitNat : Lane369Digit → Nat
digitNat digit-3 = three
digitNat digit-6 = six
digitNat digit-9 = nine

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

data Lane369Address : Nat → Set where
  root :
    Lane369Address zero

  extend :
    ∀ {d : Nat} →
    Lane369Address d →
    Lane369Digit →
    Lane369Address (suc d)

addressDepth :
  ∀ {d : Nat} →
  Lane369Address d →
  Nat
addressDepth {d} _ = d

addressDigits :
  ∀ {d : Nat} →
  Lane369Address d →
  List Lane369Digit
addressDigits root = []
addressDigits (extend path digit) =
  addressDigits path ++ (digit ∷ [])

prefix :
  ∀ {d : Nat} →
  Lane369Address (suc d) →
  Lane369Address d
prefix (extend path digit) = path

prefixDigits :
  ∀ {d : Nat} →
  Lane369Address (suc d) →
  List Lane369Digit
prefixDigits path = addressDigits (prefix path)

record SSPPrimeLane369Refinement (d : Nat) : Set where
  constructor mkSSPPrimeLane369Refinement
  field
    primeLane : SSP
    address : Lane369Address d

open SSPPrimeLane369Refinement public

refinementDepth :
  ∀ {d : Nat} →
  SSPPrimeLane369Refinement d →
  Nat
refinementDepth {d} _ = d

refine :
  ∀ {d : Nat} →
  Lane369Digit →
  SSPPrimeLane369Refinement d →
  SSPPrimeLane369Refinement (suc d)
refine digit r =
  mkSSPPrimeLane369Refinement
    (primeLane r)
    (extend (address r) digit)

refinementPrefix :
  ∀ {d : Nat} →
  SSPPrimeLane369Refinement (suc d) →
  SSPPrimeLane369Refinement d
refinementPrefix r =
  mkSSPPrimeLane369Refinement
    (primeLane r)
    (prefix (address r))

canonicalSSPPrimeLane369Lane :
  SSP
canonicalSSPPrimeLane369Lane = p3

canonicalRootLane369Refinement :
  SSPPrimeLane369Refinement zero
canonicalRootLane369Refinement =
  mkSSPPrimeLane369Refinement
    canonicalSSPPrimeLane369Lane
    root

canonicalThreeLane369Refinement :
  SSPPrimeLane369Refinement (suc zero)
canonicalThreeLane369Refinement =
  refine digit-3 canonicalRootLane369Refinement

canonicalThreeSixLane369Refinement :
  SSPPrimeLane369Refinement (suc (suc zero))
canonicalThreeSixLane369Refinement =
  refine digit-6 canonicalThreeLane369Refinement

canonicalThreeSixNineLane369Refinement :
  SSPPrimeLane369Refinement (suc (suc (suc zero)))
canonicalThreeSixNineLane369Refinement =
  refine digit-9 canonicalThreeSixLane369Refinement

canonicalThreeSixNineAddress :
  Lane369Address (suc (suc (suc zero)))
canonicalThreeSixNineAddress =
  address canonicalThreeSixNineLane369Refinement

canonicalThreeSixNinePrefix :
  prefix canonicalThreeSixNineAddress
  ≡ address canonicalThreeSixLane369Refinement
canonicalThreeSixNinePrefix = refl

canonicalThreeSixNineDigits :
  addressDigits canonicalThreeSixNineAddress
  ≡ digit-3 ∷ digit-6 ∷ digit-9 ∷ []
canonicalThreeSixNineDigits = refl

canonicalThreeSixNinePrefixDigits :
  prefixDigits canonicalThreeSixNineAddress
  ≡ digit-3 ∷ digit-6 ∷ []
canonicalThreeSixNinePrefixDigits = refl
