module DASHI.Arithmetic.CoprimeLayer where

open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.Divisibility using
  ( _∣_
  ; divides
  ; m∣n⇒n≡m*quotient
  ; ∣m⇒∣m*n
  )
open import Data.Nat.Coprimality renaming (sym to coprime-sym) using
  ( Coprime
  ; 1-coprimeTo
  ; coprime-divisor
  ; coprime-factors
  )
open import Data.Product.Base using (_,_)
open import Data.Nat.Properties using (*-assoc; *-comm)
open import Relation.Binary.PropositionalEquality using
  (_≡_; trans; cong; subst; sym)

open import DASHI.TrackedPrimes using
  ( SSP
  ; toNat
  )
open import DASHI.Arithmetic.TrackedCoprimeTable public using
  ( _≢_
  ; gcdTable
  ; gcdTable-distinct
  ; distinctTrackedBasesCoprime
  )
open import DASHI.Arithmetic.DeltaGrowth using (pow)

------------------------------------------------------------------------
-- Distinct tracked prime powers are the tracked-only arithmetic seam.
--
-- Prove it directly on the tracked carrier. We only need:
--   * tracked base coprimality from TrackedCoprimeTable
--   * divisibility transport under multiplication
--   * the stdlib coprime-factors eliminator

trackedBaseVsPrimePowerCoprime :
  ∀ p q b →
  p ≢ q →
  Coprime (toNat p) (pow (toNat q) b)
trackedBaseVsPrimePowerCoprime p q zero p≢q =
  coprime-sym (1-coprimeTo (toNat p))
trackedBaseVsPrimePowerCoprime p q (suc b) p≢q
  {d} (d∣p , d∣q*qb) =
    trackedBaseVsPrimePowerCoprime p q b p≢q
      ( d∣p
      , coprime-factors
          (distinctTrackedBasesCoprime p q p≢q)
          ( ∣m⇒∣m*n (pow (toNat q) b) d∣p
          , d∣q*qb
          )
      )

distinctTrackedPrimePowersCoprime :
  ∀ p q a b →
  p ≢ q →
  Coprime (pow (toNat p) a) (pow (toNat q) b)
distinctTrackedPrimePowersCoprime p q zero b p≢q =
  1-coprimeTo (pow (toNat q) b)
distinctTrackedPrimePowersCoprime p q (suc a) b p≢q
  {d} (d∣p*pa , d∣qb) =
    trackedBaseVsPrimePowerCoprime p q b p≢q
      ( coprime-factors
          (distinctTrackedPrimePowersCoprime p q a b p≢q)
          ( subst
              (d ∣_)
              (*-comm (toNat p) (pow (toNat p) a))
              d∣p*pa
          , ∣m⇒∣m*n (toNat p) d∣qb
          )
      , d∣qb
      )

------------------------------------------------------------------------
-- Reusable product-divisibility lemma for coprime factors.
--
-- If m and n are coprime and both divide o, then their product divides o.

coprimeProductDivides :
  ∀ m n o →
  Coprime m n →
  m ∣ o →
  n ∣ o →
  m * n ∣ o
coprimeProductDivides m n o c m∣o n∣o =
  let
    o≡m*q : o ≡ m * _∣_.quotient m∣o
    o≡m*q = m∣n⇒n≡m*quotient m∣o

    n∣m*q : n ∣ m * _∣_.quotient m∣o
    n∣m*q = subst (n ∣_) o≡m*q n∣o

    n∣q : n ∣ _∣_.quotient m∣o
    n∣q = coprime-divisor (coprime-sym c) n∣m*q

    q≡n*r : _∣_.quotient m∣o ≡ n * _∣_.quotient n∣q
    q≡n*r = m∣n⇒n≡m*quotient n∣q
  in
  divides
    (_∣_.quotient n∣q)
    (trans
      o≡m*q
      (trans
        (cong (m *_) q≡n*r)
        (trans
          (sym (*-assoc m n (_∣_.quotient n∣q)))
          (*-comm (m * n) (_∣_.quotient n∣q)))))

------------------------------------------------------------------------
-- Packaged surface.

record CoprimeLayer : Set₁ where
  field
    primePowersCoprime :
      ∀ p q a b →
      p ≢ q →
      Coprime (pow (toNat p) a) (pow (toNat q) b)
    productDivides :
      ∀ m n o →
      Coprime m n →
      m ∣ o →
      n ∣ o →
      m * n ∣ o

open CoprimeLayer public

coprimeLayer : CoprimeLayer
coprimeLayer = record
  { primePowersCoprime = distinctTrackedPrimePowersCoprime
  ; productDivides = coprimeProductDivides
  }
