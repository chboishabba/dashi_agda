module DASHI.Moonshine.FormalQSeriesOldformEigencharacterTransportExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Oldforms and degeneracy maps.
--
-- Toshitsune Miyake,
-- "Modular Forms", Springer Monographs in Mathematics, Springer, 2006.
-- DOI: 10.1007/3-540-29593-3.
-- Prime Hecke eigenforms and coefficient laws.
--
-- DASHI CONTRIBUTION
--
-- FormalQSeriesOldformDegeneracyHeckeExact proves the coefficient commuting
-- square T_l V_d = V_d T_l whenever gcd(d,l)=1.  This file derives the exact
-- consequence needed by the p=11 / level-44 oldspace programme:
--
--   if T_l a = lambda_l a,
--   then T_l(V_d a) = lambda_l(V_d a).
--
-- The proof does NOT assume function extensionality.  First prove that a
-- degeneracy target is uniquely determined coefficientwise by its source and
-- support law.  Then prove scalar multiplication preserves the degeneracy law.
-- The two targets of the commuting square are therefore equal coefficient by
-- coefficient.
--
-- Specializations d=1,2,4 show the three level-44 old copies inherit the same
-- entire good-prime Hecke eigencharacter from the level-11 source form.  This
-- removes the need for any further prime-by-prime scan on the ANALYTIC oldform
-- side.  The remaining arithmetic same-object theorem is the identification of
-- the marked quaternion permutation module with these three degeneracy copies.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
  renaming (_+_ to _+ℤ_; _*_ to _*ℤ_)
open import Data.Nat.Divisibility using (_∣_; _∣?_ ; m∣n⇒n≡m*quotient)
import Data.Integer.Tactic.RingSolver as IntRing
open import Relation.Nullary using (yes; no)

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Deg

------------------------------------------------------------------------
-- Scalar multiplication of formal q-series.
------------------------------------------------------------------------

scaleSeries : ℤ → Deg.FormalQSeries → Deg.FormalQSeries
scaleSeries k a n = k *ℤ a n

------------------------------------------------------------------------
-- A degeneracy law determines its target coefficientwise.
------------------------------------------------------------------------

degeneracyTargetUnique :
  (d : Nat) →
  (a b c : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw d a b →
  Deg.DegeneracyCoefficientLaw d a c →
  (n : Nat) → b n ≡ c n
degeneracyTargetUnique d a b c left right n with d ∣? n
... | yes d∣n =
  let
    q : Nat
    q = _∣_.quotient d∣n

    n≡d*q : n ≡ d * q
    n≡d*q = m∣n⇒n≡m*quotient d∣n
  in
  trans
    (cong b n≡d*q)
    (trans
      (Deg.onMultiple left q)
      (trans
        (sym (Deg.onMultiple right q))
        (sym (cong c n≡d*q))))
... | no d∤n =
  trans
    (Deg.offSupport left n d∤n)
    (sym (Deg.offSupport right n d∤n))

------------------------------------------------------------------------
-- Scalar multiplication commutes with degeneracy.
------------------------------------------------------------------------

scalePreservesDegeneracy :
  (d : Nat) →
  (k : ℤ) →
  (a b : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw d a b →
  Deg.DegeneracyCoefficientLaw d (scaleSeries k a) (scaleSeries k b)
scalePreservesDegeneracy d k a b law = record
  { Deg.onMultiple = λ n → cong (k *ℤ_) (Deg.onMultiple law n)
  ; Deg.offSupport = λ n d∤n →
      trans
        (cong (k *ℤ_) (Deg.offSupport law n d∤n))
        (IntRing.solve (k ∷ []))
  }
  where
  open import Agda.Builtin.List using ([]; _∷_)

------------------------------------------------------------------------
-- Main eigencharacter transport theorem.
------------------------------------------------------------------------

goodPrimeEigencharacterTransport :
  (d ell : Nat) →
  Data.Nat.Coprimality.Coprime d ell →
  (lambda : ℤ) →
  (a b Ta Tb : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw d a b →
  Deg.Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Deg.Weight2PrimeHeckeCoefficientLaw ell b Tb →
  ((n : Nat) → Ta n ≡ scaleSeries lambda a n) →
  (n : Nat) → Tb n ≡ scaleSeries lambda b n
goodPrimeEigencharacterTransport d ell cop lambda a b Ta Tb deg heckeA heckeB sourceEigen =
  degeneracyTargetUnique d (scaleSeries lambda a) Tb (scaleSeries lambda b)
    transportedTarget
    scaledTarget
  where
  commuting : Deg.DegeneracyCoefficientLaw d Ta Tb
  commuting = Deg.oldformDegeneracyCommutesWithGoodPrime
    d ell cop a b Ta Tb deg heckeA heckeB

  transportedTarget :
    Deg.DegeneracyCoefficientLaw d (scaleSeries lambda a) Tb
  transportedTarget = record
    { Deg.onMultiple = λ n →
        trans (Deg.onMultiple commuting n) (sourceEigen n)
    ; Deg.offSupport = Deg.offSupport commuting
    }

  scaledTarget :
    Deg.DegeneracyCoefficientLaw d
      (scaleSeries lambda a) (scaleSeries lambda b)
  scaledTarget = scalePreservesDegeneracy d lambda a b deg

------------------------------------------------------------------------
-- Level 44: d=1,2,4 all inherit the same good-prime character.
------------------------------------------------------------------------

degeneracy1PreservesEigencharacter :
  (ell : Nat) →
  (lambda : ℤ) →
  (a b Ta Tb : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw 1 a b →
  Deg.Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Deg.Weight2PrimeHeckeCoefficientLaw ell b Tb →
  ((n : Nat) → Ta n ≡ scaleSeries lambda a n) →
  (n : Nat) → Tb n ≡ scaleSeries lambda b n
degeneracy1PreservesEigencharacter ell =
  goodPrimeEigencharacterTransport 1 ell
    (Data.Nat.Coprimality.1-coprimeTo ell)

degeneracy2PreservesEigencharacter :
  (ell : Nat) →
  Deg.PrimeToLevel44Auxiliary ell →
  (lambda : ℤ) →
  (a b Ta Tb : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw 2 a b →
  Deg.Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Deg.Weight2PrimeHeckeCoefficientLaw ell b Tb →
  ((n : Nat) → Ta n ≡ scaleSeries lambda a n) →
  (n : Nat) → Tb n ≡ scaleSeries lambda b n
degeneracy2PreservesEigencharacter ell good =
  goodPrimeEigencharacterTransport 2 ell (Deg.coprime2 good)

degeneracy4PreservesEigencharacter :
  (ell : Nat) →
  Deg.PrimeToLevel44Auxiliary ell →
  (lambda : ℤ) →
  (a b Ta Tb : Deg.FormalQSeries) →
  Deg.DegeneracyCoefficientLaw 4 a b →
  Deg.Weight2PrimeHeckeCoefficientLaw ell a Ta →
  Deg.Weight2PrimeHeckeCoefficientLaw ell b Tb →
  ((n : Nat) → Ta n ≡ scaleSeries lambda a n) →
  (n : Nat) → Tb n ≡ scaleSeries lambda b n
degeneracy4PreservesEigencharacter ell good =
  goodPrimeEigencharacterTransport 4 ell (Deg.coprime4 good)

record FormalQSeriesOldformEigencharacterBoundary : Set where
  field
    degeneracyTargetUniquenessProved : Bool
    scalarDegeneracyCompatibilityProved : Bool
    genericGoodPrimeEigenTransportProved : Bool
    level44ThreeCopyEigenTransportProved : Bool
    furtherPrimeScanningNeededForAnalyticOldspace : Bool
    markedQuaternionSameObjectIdentificationProvedHere : Bool

canonicalFormalQSeriesOldformEigencharacterBoundary :
  FormalQSeriesOldformEigencharacterBoundary
canonicalFormalQSeriesOldformEigencharacterBoundary = record
  { degeneracyTargetUniquenessProved = true
  ; scalarDegeneracyCompatibilityProved = true
  ; genericGoodPrimeEigenTransportProved = true
  ; level44ThreeCopyEigenTransportProved = true
  ; furtherPrimeScanningNeededForAnalyticOldspace = false
  ; markedQuaternionSameObjectIdentificationProvedHere = false
  }
