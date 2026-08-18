module DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Oldforms, degeneracy maps, and Hecke operators away from the added level.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
-- Classical coefficient formula for prime Hecke operators.
--
-- DASHI CONTRIBUTION
--
-- Construct the coefficient-level theorem needed by the live p=11/level-44
-- oldspace weld instead of importing "old copies have the same eigenvalue" as
-- a receipt.
--
-- A formal q-series is an integer coefficient function a : Nat -> Z.
-- Degeneracy by d is characterized source-natively by
--
--   (V_d a)_(d n) = a_n,
--   (V_d a)_m = 0 when d does not divide m.
--
-- The normalized weight-2 prime Hecke coefficient law is
--
--   (T_l a)_n = a_(l n) + l a_q    when n = l q,
--   (T_l a)_n = a_(l n)            when l does not divide n.
--
-- We prove constructively that if gcd(d,l)=1, then any two series satisfying
-- these laws obey the exact coefficient commuting square T_l V_d = V_d T_l at
-- EVERY coefficient, including off-support coefficients.  Coprimality is used
-- to prove multiplication by l cannot create either d-support or hidden l-
-- divisibility.
--
-- Specializing d=1,2,4 gives exactly the three degeneracy copies used when
-- level 11 is raised to level 44.  This is the analytic/formal-q-series half of
-- the same-object theorem; identifying those copies with the marked quaternion
-- permutation module remains a separate geometric/Jacquet-Langlands map.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Nat.Divisibility using
  (_∣_; _∣?_; m∣n⇒n≡m*quotient; ∣n⇒∣m*n)
open import Data.Nat.Coprimality using
  (Coprime; 1-coprimeTo; coprime-divisor)
  renaming (sym to coprime-sym)
import Data.Nat.Tactic.RingSolver as NatRing
import Data.Integer.Tactic.RingSolver as IntRing
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

FormalQSeries : Set
FormalQSeries = Nat → ℤ

record DegeneracyCoefficientLaw
  (d : Nat) (source target : FormalQSeries) : Set where
  field
    onMultiple : (n : Nat) → target (d * n) ≡ source n
    offSupport : (n : Nat) → ¬ (d ∣ n) → target n ≡ + 0

open DegeneracyCoefficientLaw public

record Weight2PrimeHeckeCoefficientLaw
  (ell : Nat) (source target : FormalQSeries) : Set where
  field
    onDivisible :
      (n q : Nat) →
      n ≡ ell * q →
      target n ≡ source (ell * n) +ℤ ((+ ell) *ℤ source q)

    onNondivisible :
      (n : Nat) →
      ¬ (ell ∣ n) →
      target n ≡ source (ell * n)

open Weight2PrimeHeckeCoefficientLaw public

coprimeCannotCreateSupport :
  (d ell n : Nat) →
  Coprime d ell →
  ¬ (d ∣ n) →
  ¬ (d ∣ ell * n)
coprimeCannotCreateSupport d ell n cop d∤n d∣ell*n =
  d∤n (coprime-divisor cop d∣ell*n)

coprimeCannotCreatePrimeDivisibility :
  (d ell n : Nat) →
  Coprime d ell →
  ¬ (ell ∣ n) →
  ¬ (ell ∣ d * n)
coprimeCannotCreatePrimeDivisibility d ell n cop ell∤n ell∣d*n =
  ell∤n (coprime-divisor (coprime-sym cop) ell∣d*n)

oldformDegeneracyCommutesWithGoodPrime :
  (d ell : Nat) →
  Coprime d ell →
  (a b Ta Tb : FormalQSeries) →
  DegeneracyCoefficientLaw d a b →
  Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Weight2PrimeHeckeCoefficientLaw ell b Tb →
  DegeneracyCoefficientLaw d Ta Tb
oldformDegeneracyCommutesWithGoodPrime d ell cop a b Ta Tb deg heckeA heckeB =
  record
    { onMultiple = commutingMultiple
    ; offSupport = commutingOffSupport
    }
  where
  firstTermDegenerates :
    (n : Nat) → b (ell * (d * n)) ≡ a (ell * n)
  firstTermDegenerates n =
    trans
      (cong b (NatRing.solve (d ∷ ell ∷ n ∷ [])))
      (onMultiple deg (ell * n))

  commutingMultiple : (n : Nat) → Tb (d * n) ≡ Ta n
  commutingMultiple n with ell ∣? n
  ... | yes ell∣n =
    let
      q : Nat
      q = _∣_.quotient ell∣n

      n≡ell*q : n ≡ ell * q
      n≡ell*q = m∣n⇒n≡m*quotient ell∣n

      dn≡ell*dq : d * n ≡ ell * (d * q)
      dn≡ell*dq =
        trans
          (cong (d *_) n≡ell*q)
          (NatRing.solve (d ∷ ell ∷ q ∷ []))

      first : b (ell * (d * n)) ≡ a (ell * n)
      first = firstTermDegenerates n

      second : b (d * q) ≡ a q
      second = onMultiple deg q
    in
    trans
      (onDivisible heckeB (d * n) (d * q) dn≡ell*dq)
      (trans
        (cong₂
          (λ x y → x +ℤ ((+ ell) *ℤ y))
          first second)
        (sym (onDivisible heckeA n q n≡ell*q)))

  ... | no ell∤n =
    let
      ell∤dn : ¬ (ell ∣ d * n)
      ell∤dn = coprimeCannotCreatePrimeDivisibility d ell n cop ell∤n
    in
    trans
      (onNondivisible heckeB (d * n) ell∤dn)
      (trans
        (firstTermDegenerates n)
        (sym (onNondivisible heckeA n ell∤n)))

  commutingOffSupport :
    (m : Nat) → ¬ (d ∣ m) → Tb m ≡ + 0
  commutingOffSupport m d∤m with ell ∣? m
  ... | yes ell∣m =
    let
      q : Nat
      q = _∣_.quotient ell∣m

      m≡ell*q : m ≡ ell * q
      m≡ell*q = m∣n⇒n≡m*quotient ell∣m

      d∤ell*m : ¬ (d ∣ ell * m)
      d∤ell*m = coprimeCannotCreateSupport d ell m cop d∤m

      d∤q : ¬ (d ∣ q)
      d∤q d∣q =
        d∤m
          (subst
            (d ∣_)
            (sym m≡ell*q)
            (∣n⇒∣m*n ell d∣q))

      firstZero : b (ell * m) ≡ + 0
      firstZero = offSupport deg (ell * m) d∤ell*m

      secondZero : b q ≡ + 0
      secondZero = offSupport deg q d∤q
    in
    trans
      (onDivisible heckeB m q m≡ell*q)
      (trans
        (cong₂
          (λ x y → x +ℤ ((+ ell) *ℤ y))
          firstZero secondZero)
        (IntRing.solve []))

  ... | no ell∤m =
    let
      d∤ell*m : ¬ (d ∣ ell * m)
      d∤ell*m = coprimeCannotCreateSupport d ell m cop d∤m
    in
    trans
      (onNondivisible heckeB m ell∤m)
      (offSupport deg (ell * m) d∤ell*m)

------------------------------------------------------------------------
-- Exactly the three level-44 degeneracy copies d=1,2,4.
------------------------------------------------------------------------

record PrimeToLevel44Auxiliary (ell : Nat) : Set where
  field
    coprime2 : Coprime 2 ell
    coprime4 : Coprime 4 ell

open PrimeToLevel44Auxiliary public

degeneracy1Commutes :
  (ell : Nat) →
  (a b Ta Tb : FormalQSeries) →
  DegeneracyCoefficientLaw 1 a b →
  Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Weight2PrimeHeckeCoefficientLaw ell b Tb →
  DegeneracyCoefficientLaw 1 Ta Tb
degeneracy1Commutes ell =
  oldformDegeneracyCommutesWithGoodPrime 1 ell (1-coprimeTo ell)

degeneracy2Commutes :
  (ell : Nat) →
  PrimeToLevel44Auxiliary ell →
  (a b Ta Tb : FormalQSeries) →
  DegeneracyCoefficientLaw 2 a b →
  Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Weight2PrimeHeckeCoefficientLaw ell b Tb →
  DegeneracyCoefficientLaw 2 Ta Tb
degeneracy2Commutes ell good =
  oldformDegeneracyCommutesWithGoodPrime 2 ell (coprime2 good)

degeneracy4Commutes :
  (ell : Nat) →
  PrimeToLevel44Auxiliary ell →
  (a b Ta Tb : FormalQSeries) →
  DegeneracyCoefficientLaw 4 a b →
  Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Weight2PrimeHeckeCoefficientLaw ell b Tb →
  DegeneracyCoefficientLaw 4 Ta Tb
degeneracy4Commutes ell good =
  oldformDegeneracyCommutesWithGoodPrime 4 ell (coprime4 good)

record FormalQSeriesOldformDegeneracyBoundary : Set where
  field
    coefficientDegeneracyLawConstructed : Bool
    weight2PrimeHeckeLawConstructed : Bool
    genericCoprimeCommutationProved : Bool
    level44CopiesOneTwoFourSpecialized : Bool
    analyticEtaOrModularFormObjectRequired : Bool
    markedQuaternionSameObjectMapConstructedHere : Bool

canonicalFormalQSeriesOldformDegeneracyBoundary :
  FormalQSeriesOldformDegeneracyBoundary
canonicalFormalQSeriesOldformDegeneracyBoundary = record
  { coefficientDegeneracyLawConstructed = true
  ; weight2PrimeHeckeLawConstructed = true
  ; genericCoprimeCommutationProved = true
  ; level44CopiesOneTwoFourSpecialized = true
  ; analyticEtaOrModularFormObjectRequired = false
  ; markedQuaternionSameObjectMapConstructedHere = false
  }
