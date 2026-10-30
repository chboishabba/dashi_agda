module DASHI.Arithmetic.TwinPrimeMangoldtProperPowerCandidateCoverageExact where

------------------------------------------------------------------------
-- CT11 -> M15: ACTUAL VON-MANGOLDT ERROR SUPPORT LANDS IN THE
-- COMPUTED, DUPLICATE-FREE PROPER-POWER CANDIDATE IMAGE.
--
-- Original owners (import-only):
--   RiemannVonMangoldtSpecification / RiemannPrimePowerArithmetic
--   TwinPrimeMangoldtErrorSupportProperExact
--   TwinPrimeProperPowerUniversalRectangleCoverageExact
--
-- The abstract AllPrimeArithmetic carrier contains a Nat readout but
-- does NOT, by itself, prove that its numbers are >= 2.  Hence the
-- sole explicit bridge below is a proof-relevant positive-base
-- decomposition. The original ChebyshevPrimeOwnership and
-- NatPrimality refutations of zero and one discharge it below.
--
-- No counting of interval positions, ordered logarithmic weights,
-- signed cancellation or positive prime correlation is asserted.
-- Source-written; Agda kernel and transitive --safe check pending.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_≤_)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Nat.Properties as NP
import Data.Nat.Primality as NatPrime
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

import DASHI.Analysis.WeilTestSpace as Weil
import DASHI.Analysis.RiemannVonMangoldtSpecification as VM
import DASHI.Analysis.RiemannPrimePowerArithmetic as Power
import DASHI.Analysis.ChebyshevPrimeCounting as Cheb
import DASHI.Analysis.NatPrimeCountingInstance as PrimeNat
import DASHI.Arithmetic.TwinPrimeMangoldtErrorSupportProperExact as Support
import DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact as Split
import DASHI.Arithmetic.TwinPrimeMangoldtOutsidePrimePowersZeroExact as Zero
import DASHI.Arithmetic.TwinPrimeProperPowerUniversalRectangleCoverageExact as Cover
import DASHI.Arithmetic.TwinPrimeProperPowerRectangleEnumerationExact as Rect
import DASHI.Arithmetic.TwinPrimeProperPowerBinaryCutoffNatExact as Binary
import DASHI.Mathematics.NumberTheory.FiniteNatFloorSquareRootExact as Root

record PrimeBaseAtLeastTwo
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space) : Set where
  field
    baseAsTwoPlus :
      (p : VM.AllPrimeArithmetic.Prime arithmetic) →
      Σ Nat (λ predecessor →
        VM.AllPrimeArithmetic.toNat arithmetic p ≡ suc (suc predecessor))

------------------------------------------------------------------------
-- Discharge the positive-base bridge from an ALREADY-OWNED genuine
-- all-prime <-> NatPrime identity. This consumes real NatPrime evidence
-- and the standard library's refutations of 0 and 1 as primes.
------------------------------------------------------------------------

natPrimeBaseAsTwoPlus :
  (n : Nat) →
  NatPrime.Prime n →
  Σ Nat (λ predecessor → n ≡ suc (suc predecessor))
natPrimeBaseAsTwoPlus zero prime =
  ⊥-elim (NatPrime.¬prime[0] prime)
natPrimeBaseAsTwoPlus (suc zero) prime =
  ⊥-elim (NatPrime.¬prime[1] prime)
natPrimeBaseAsTwoPlus (suc (suc predecessor)) prime =
  predecessor , refl

primeBaseFromChebyshevOwnership :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic) →
  PrimeBaseAtLeastTwo space arithmetic
primeBaseFromChebyshevOwnership space arithmetic theta ownership =
  record
    { baseAsTwoPlus = λ p →
        natPrimeBaseAsTwoPlus
          (VM.AllPrimeArithmetic.toNat arithmetic p)
          (Cheb.ChebyshevPrimeOwnership.carrierIsPrime ownership p)
    }

computedProperPowerCandidates : Nat → List Nat
computedProperPowerCandidates upper =
  Rect.dedupPowerValues
    (Rect.powerValueRectangle
      (Root.floorSquareRoot upper)
      (Binary.floorBinaryExponent upper))

-- This is a genuine membership theorem for the *original* all-prime
-- carrier after the necessary numeric base-identity obligation.
properPowerAtCovered :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (baseBridge : PrimeBaseAtLeastTwo space arithmetic)
  (n upper : Nat) →
  Support.ProperPowerAt space arithmetic n →
  n ≤ upper →
  Rect._member_ n (computedProperPowerCandidates upper)
properPowerAtCovered space arithmetic baseBridge n upper
    (Support.proper-power-at p k equality) bounded
  with PrimeBaseAtLeastTwo.baseAsTwoPlus baseBridge p
... | predecessor , baseEq =
  subst
    (λ value → Rect._member_ value (computedProperPowerCandidates upper))
    (sym powerEquality)
    (Cover.properPowerInDedupComputedRectangle
      predecessor k upper
      (subst (λ value → value ≤ upper) powerEquality bounded))
  where
    powerEquality :
      n ≡ Power.natPow (suc (suc predecessor)) (suc (suc k))
    powerEquality =
      trans equality
        (cong (λ base → Power.natPow base (suc (suc k))) baseEq)

-- Every nonzero residual in a bounded shifted pair uses one of the
-- SAME values in the computed candidate image, not an SSP/CRT proxy.
nonzeroErrorEndpointInCandidateImage :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic)
  (baseBridge : PrimeBaseAtLeastTwo space arithmetic)
  (n upper : Nat) →
  n + 2 ≤ upper →
  (Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space → ⊥) →
  (Rect._member_ n (computedProperPowerCandidates upper))
    ⊎
  (Rect._member_ (n + 2) (computedProperPowerCandidates upper))
nonzeroErrorEndpointInCandidateImage space arithmetic mangoldt
    zeroLaws baseBridge n upper rightBound nonzero
  with Support.errorNonzeroHasProperPower
    space arithmetic mangoldt zeroLaws n nonzero
... | Support.leftProper pp =
  inj₁ (properPowerAtCovered space arithmetic baseBridge n upper
    pp (NP.≤-trans (NP.m≤m+n n 2) rightBound))
... | Support.rightProper pp =
  inj₂ (properPowerAtCovered space arithmetic baseBridge (n + 2)
    upper pp rightBound)

-- Converse support exclusion: no candidate value at either endpoint
-- forces the exact retained residual to zero.
errorZeroOutsideComputedCandidateImage :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic)
  (baseBridge : PrimeBaseAtLeastTwo space arithmetic)
  (n upper : Nat) →
  n + 2 ≤ upper →
  (Rect._member_ n (computedProperPowerCandidates upper) → ⊥) →
  (Rect._member_ (n + 2) (computedProperPowerCandidates upper) → ⊥) →
  Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space
errorZeroOutsideComputedCandidateImage space arithmetic mangoldt
    zeroLaws baseBridge n upper rightBound leftAbsent rightAbsent =
  Support.errorZeroIfNoProper space arithmetic mangoldt zeroLaws n
    (λ { (Support.leftProper pp) →
           leftAbsent (properPowerAtCovered space arithmetic
             baseBridge n upper pp
             (NP.≤-trans (NP.m≤m+n n 2) rightBound))
       ; (Support.rightProper pp) →
           rightAbsent (properPowerAtCovered space arithmetic
             baseBridge (n + 2) upper pp rightBound)
       })

------------------------------------------------------------------------
-- CT11/M15 without an additional positive-base premise: the exact
-- original Chebyshev ownership proof supplies the base decomposition.
------------------------------------------------------------------------

nonzeroErrorEndpointFromCertifiedOwnership :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic)
  (n upper : Nat) →
  n + 2 ≤ upper →
  (Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space → ⊥) →
  (Rect._member_ n (computedProperPowerCandidates upper))
    ⊎
  (Rect._member_ (n + 2) (computedProperPowerCandidates upper))
nonzeroErrorEndpointFromCertifiedOwnership space arithmetic mangoldt
    theta ownership zeroLaws n upper endBound nonzero =
  nonzeroErrorEndpointInCandidateImage space arithmetic mangoldt
    zeroLaws
    (primeBaseFromChebyshevOwnership space arithmetic theta ownership)
    n upper endBound nonzero

errorZeroOutsideImageFromCertifiedOwnership :
  (space : Weil.WeilTestSpace)
  (arithmetic : VM.AllPrimeArithmetic space)
  (mangoldt : VM.VonMangoldtFunction space arithmetic)
  (theta : Cheb.PrimeLogWeightKernel space PrimeNat.natPrimePredicate)
  (ownership : Cheb.ChebyshevPrimeOwnership
    space PrimeNat.natPrimePredicate theta arithmetic)
  (zeroLaws : Zero.ProductZeroLaws space arithmetic)
  (n upper : Nat) →
  n + 2 ≤ upper →
  (Rect._member_ n (computedProperPowerCandidates upper) → ⊥) →
  (Rect._member_ (n + 2) (computedProperPowerCandidates upper) → ⊥) →
  Split.nonPrimeErrorAtNat space arithmetic mangoldt n
    ≡ Weil.WeilTestSpace.zeroS space
errorZeroOutsideImageFromCertifiedOwnership space arithmetic mangoldt
    theta ownership zeroLaws n upper endBound notLeft notRight =
  errorZeroOutsideComputedCandidateImage space arithmetic mangoldt
    zeroLaws
    (primeBaseFromChebyshevOwnership space arithmetic theta ownership)
    n upper endBound notLeft notRight
