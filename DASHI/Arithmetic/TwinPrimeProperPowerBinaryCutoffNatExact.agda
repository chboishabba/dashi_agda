module DASHI.Arithmetic.TwinPrimeProperPowerBinaryCutoffNatExact where

------------------------------------------------------------------------
-- CT11: TOTAL NAT COMPUTED EXPONENT CUTOFF; NO REAL LOG.
--
-- Reuses original numeric 2^e:
-- DASHI.Core.GeneralResidualFibreCardinalityExact.pow2
-- and the bounded-maximality pattern owned by
-- DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact.
--
-- For EVERY Nat U,e, 2^e <= U implies
-- e <= floorBinaryExponent U.  The cutoff is a finite bounded
-- search over [0,U], rather than a quoted logarithmic estimate.
--
-- Source-written (kernel check pending); no new postulates.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _^_; z≤n; s≤s)
import Data.Nat.Logarithm as Log
open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat.Properties as NP
open import Relation.Binary.PropositionalEquality using
  (_≢_; cong; subst; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Core.GeneralResidualFibreCardinalityExact as Core
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Root
import DASHI.Arithmetic.TwinPrimeProperPowerCoreBinaryCapacityReuseExact as Binary
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power

doubleAsTwoTimes : (n : Nat) → n + n ≡ 2 * n
doubleAsTwoTimes n =
  sym (cong (n +_) (NP.+-identityʳ n))

onePlusAsSuc : (n : Nat) → n + suc zero ≡ suc n
onePlusAsSuc n =
  trans (NP.+-suc n zero) (cong suc (NP.+-identityʳ n))

positiveBinaryPower : (e : Nat) → suc zero ≤ Core.pow2 e
positiveBinaryPower zero = NP.≤-refl
positiveBinaryPower (suc e) =
  NP.≤-trans
    (positiveBinaryPower e)
    (subst (λ bound → Core.pow2 e ≤ bound)
      (doubleAsTwoTimes (Core.pow2 e))
      (NP.m≤m+n (Core.pow2 e) (Core.pow2 e)))

sucLeDouble :
  (n : Nat) →
  suc zero ≤ n →
  suc n ≤ 2 * n
sucLeDouble n positive =
  subst
    (λ bound → suc n ≤ bound)
    (doubleAsTwoTimes n)
    (subst (λ left → left ≤ n + n)
      (onePlusAsSuc n)
      (NP.+-mono-≤ NP.≤-refl positive))

exponentLeBinaryPower :
  (e : Nat) →
  e ≤ Core.pow2 e
exponentLeBinaryPower zero = z≤n
exponentLeBinaryPower (suc e) =
  NP.≤-trans
    (s≤s (exponentLeBinaryPower e))
    (sucLeDouble (Core.pow2 e) (positiveBinaryPower e))

-- The exact finite search may return zero for U=0; this is sound:
-- no exponent with positive 2^e can satisfy 2^e<=0.
floorBinaryExponentUpTo : Nat → Nat → Nat
floorBinaryExponentUpTo upper zero = zero
floorBinaryExponentUpTo upper (suc bound)
  with Core.pow2 (suc bound) NP.≤? upper
... | yes fits = suc bound
... | no tooLarge = floorBinaryExponentUpTo upper bound

binaryExponentUpToMaximal :
  ∀ {upper bound candidate : Nat} →
  candidate ≤ bound →
  Core.pow2 candidate ≤ upper →
  candidate ≤ floorBinaryExponentUpTo upper bound
binaryExponentUpToMaximal {upper} {zero} {zero}
    bound candidateFits = z≤n
binaryExponentUpToMaximal {upper} {zero} {suc candidate}
    () candidateFits
binaryExponentUpToMaximal {upper} {suc bound} {candidate}
    candidateBound candidateFits
  with Core.pow2 (suc bound) NP.≤? upper
... | yes fits = candidateBound
... | no tooLarge =
  binaryExponentUpToMaximal
    (Root.strictBelowSuccessorToLe
      (Root.strictFromLeDifferent candidateBound notTop))
    candidateFits
  where
    notTop : candidate ≢ suc bound
    notTop equality =
      tooLarge
        (subst
          (λ e → Core.pow2 e ≤ upper)
          equality candidateFits)

floorBinaryExponent : Nat → Nat
floorBinaryExponent upper =
  floorBinaryExponentUpTo upper upper

binaryPowerExponentBelowCutoff :
  (upper exponent : Nat) →
  Core.pow2 exponent ≤ upper →
  exponent ≤ floorBinaryExponent upper
binaryPowerExponentBelowCutoff upper exponent fits =
  binaryExponentUpToMaximal
    (NP.≤-trans (exponentLeBinaryPower exponent) fits)
    fits

properPowerExponentBelowCutoff :
  (basePredecessor k upper : Nat) →
  Power.natPow
    (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  suc k ≤ floorBinaryExponent upper
properPowerExponentBelowCutoff basePredecessor k upper bound =
  NP.≤-trans
    (NP.n≤1+n (suc k))
    (binaryPowerExponentBelowCutoff upper (suc (suc k))
      (Binary.properPowerNeedsCoreBinaryCapacity
        basePredecessor k upper bound))

------------------------------------------------------------------------
-- CT11 PARETO REUSE: THE EXISTING STANDARD-LIBRARY FLOOR LOG₂ IS A
-- PROVED UNIVERSAL EXPONENT CUTOFF, NOT A NEW REAL LOG AUTHORITY.
--
-- Original stdlib owners: Data.Nat.Logarithm.⌊log₂⌋-mono-≤,
-- ⌊log₂[2^n]⌋≡n. The same library is already imported by DASHI's
-- NSTriadKNCeilLogShellBounds / LiteralDyadicShellConstants.
-- Retain the previous executable floorBinaryExponent for clients;
-- use this canonical stdlib mathematical bound where convenient.
------------------------------------------------------------------------

stdlibPowTwoEqualsCore :
  (e : Nat) → 2 ^ e ≡ Core.pow2 e
stdlibPowTwoEqualsCore zero = refl
stdlibPowTwoEqualsCore (suc e) =
  cong (2 *_) (stdlibPowTwoEqualsCore e)

canonicalStdlibFloorLog₂ : Nat → Nat
canonicalStdlibFloorLog₂ upper = Log.⌊log₂ upper ⌋

binaryPowerExponentBelowStdlibLog :
  (upper exponent : Nat) →
  Core.pow2 exponent ≤ upper →
  exponent ≤ canonicalStdlibFloorLog₂ upper
binaryPowerExponentBelowStdlibLog upper exponent fits =
  subst
    (λ idx → idx ≤ canonicalStdlibFloorLog₂ upper)
    (Log.⌊log₂[2^n]⌋≡n exponent)
    (Log.⌊log₂⌋-mono-≤
      (subst (λ value → value ≤ upper)
        (sym (stdlibPowTwoEqualsCore exponent)) fits))

properPowerExponentBelowStdlibLog :
  (basePredecessor k upper : Nat) →
  Power.natPow (suc (suc basePredecessor)) (suc (suc k))
    ≤ upper →
  suc k ≤ canonicalStdlibFloorLog₂ upper
properPowerExponentBelowStdlibLog basePredecessor k upper bound =
  NP.≤-trans
    (NP.n≤1+n (suc k))
    (binaryPowerExponentBelowStdlibLog upper (suc (suc k))
      (Binary.properPowerNeedsCoreBinaryCapacity
        basePredecessor k upper bound))
