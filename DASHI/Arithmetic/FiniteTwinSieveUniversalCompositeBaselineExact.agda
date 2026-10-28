module DASHI.Arithmetic.FiniteTwinSieveUniversalCompositeBaselineExact where

------------------------------------------------------------------------
-- SOURCE / AUTHORSHIP
--
-- Classical finite-sieve arithmetic, Brun; Selberg parity limitation;
-- DHJ Polymath (2014), Variants of the Selberg sieve...
-- Reuses the original DASHI proof owners:
--   CertifiedPrimePairModulusExact.LocalPairSurvives / AllPairSurvive
--   CertifiedPrimePairPeriodExact.CommonPeriod / productIsCommonPeriod
--   FiniteTwinSieveFactorableLiftExact.factored composite lift.
-- Uses standard-library Data.Nat.Divisibility modular equivalence.
--
-- NEW:
--  Any finite certified prime list has the explicit survivor 2P-1,
--  P=product of its moduli (or r=1 for empty list).
--  For every NONEMPTY list P>=2, and every t>=1, the previous
--  source-written factorable lift yields a genuine pair of two
--  stdlib-Composite, hence non-Prime, sieve-surviving integers.
--
-- This eliminates the formerly assumed baseline r>=2 witness,
-- and DOES NOT require the general CRT inverse, analytic prime
-- distribution, or a FRACTRAN universal simulation.
--
-- Unboundedness/injectivity in t is a distinct future formal lemma.
-- New Agda code remains kernel-pending. No postulates or escape flags.
-- Original Ibrahim Monster 3B / 4B, SSP and FRACDASH owners retained.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Agda.Builtin.Unit using (tt)
open import Relation.Binary.PropositionalEquality using
  (_≢_; sym; trans; subst; cong; cong₂)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import Data.Nat.Divisibility as Div
open import Data.Nat.DivMod using (_%_)
import Data.Nat.Primality as Prime
import DASHI.Arithmetic.CertifiedPrimePairModulusExact as Pair
import DASHI.Arithmetic.CertifiedPrimePairPeriodExact as Period
import DASHI.Arithmetic.FiniteTwinSieveFactorableLiftExact as Lift

-- When P=suc b, this is 2P−1. The representation avoids Nat
-- underflow and explicitly retains prime 2 when it divides P.
baselineMinusOne : Nat → Nat
baselineMinusOne b = suc (2 * b)

baselinePlusOne :
  (b : Nat) →
  baselineMinusOne b + 1 ≡ 2 * (suc b)
baselinePlusOne =
  solve 1
    (λ b →
      (con 1 :+ (con 2 :* b)) :+ con 1
      := con 2 :* (con 1 :+ b))
    refl

baselinePlusTwo :
  (b : Nat) →
  baselineMinusOne b + 2 ≡ 2 * (suc b) + 1
baselinePlusTwo =
  solve 1
    (λ b →
      (con 1 :+ (con 2 :* b)) :+ con 2
      := (con 2 :* (con 1 :+ b)) :+ con 1)
    refl

axisPrimeCannotBeOne :
  (axis : Pair.CertifiedPrimeAxis) →
  Pair.primeModulus axis ≢ 1
axisPrimeCannotBeOne axis equality =
  Prime.¬prime[1]
    (subst Prime.Prime equality (Pair.primeWitness axis))

-- If p divides P, neither 2P−1 nor 2P+1 is divisible by p.
-- Any counterexample would make p divide 1, contradicting Prime p.
baselineLocalPairSurvives :
  (axis : Pair.CertifiedPrimeAxis) →
  (b : Nat) →
  Pair.primeModulus axis Div.∣ suc b →
  Pair.LocalPairSurvives axis (baselineMinusOne b)
baselineLocalPairSurvives axis b dividesPeriod =
  leftNonzero , rightNonzero
  where
    p : Nat
    p = Pair.primeModulus axis

    pDividesDoublePeriod : p Div.∣ 2 * suc b
    pDividesDoublePeriod =
      Div.∣n⇒∣m*n 2 dividesPeriod

    pDividesBaselinePlusOne : p Div.∣ (baselineMinusOne b + 1)
    pDividesBaselinePlusOne =
      subst (p Div.∣_)
        (sym (baselinePlusOne b)) pDividesDoublePeriod

    absurdDividesOne : p Div.∣ 1 → ⊥
    absurdDividesOne dividesOne =
      axisPrimeCannotBeOne axis (Div.∣1⇒≡1 dividesOne)

    leftNonzero : baselineMinusOne b % p ≢ 0
    leftNonzero remainderZero =
      absurdDividesOne
        (Div.∣m+n∣m⇒∣n
          pDividesBaselinePlusOne
          (Div.m%n≡0⇒n∣m (baselineMinusOne b) p remainderZero))

    rightNonzero : (baselineMinusOne b + 2) % p ≢ 0
    rightNonzero remainderZero =
      absurdDividesOne
        (Div.∣m+n∣m⇒∣n
          (subst (p Div.∣_)
            (baselinePlusTwo b)
            (Div.m%n≡0⇒n∣m
              (baselineMinusOne b + 2) p remainderZero))
          pDividesDoublePeriod)

-- CommonPeriod already carries each axis's p|P witness. We do not
-- need to reconstruct residue tuples or require distinct prime axes.
baselineAllPairSurvivesAtCommonPeriod :
  (axes : List Pair.CertifiedPrimeAxis) →
  (b : Nat) →
  Period.CommonPeriod axes (suc b) →
  Pair.AllPairSurvive axes (baselineMinusOne b)
baselineAllPairSurvivesAtCommonPeriod [] b period = tt
baselineAllPairSurvivesAtCommonPeriod (axis ∷ rest) b
    (Period.appendPeriod quotient divisible restProof) =
  baselineLocalPairSurvives axis b (Div.divides quotient divisible)
  ,
  baselineAllPairSurvivesAtCommonPeriod rest b restProof

anyFinitePrimeSieveHasBaseline :
  (axes : List Pair.CertifiedPrimeAxis) →
  Σ Nat (λ b →
    Pair.AllPairSurvive axes (baselineMinusOne b))
anyFinitePrimeSieveHasBaseline axes
  with Lift.certifiedModulusProductPositive axes
... | b , positive =
  b ,
  baselineAllPairSurvivesAtCommonPeriod axes b
    (subst (Period.CommonPeriod axes) positive
      (Period.productIsCommonPeriod axes))

-- An axis with a Prime certificate has modulus >=2. There is no
-- zero-residue-factor (modulus=1) in CertifiedPrimeAxis.
axisHasAtLeastTwo :
  (axis : Pair.CertifiedPrimeAxis) →
  Σ Nat (λ c → Pair.primeModulus axis ≡ suc (suc c))
axisHasAtLeastTwo axis with Pair.nonzeroResidues axis
... | zero = ⊥-elim (Prime.¬prime[1] (Pair.primeWitness axis))
... | suc c = c , refl

-- For a NONEMPTY prime-axis list, the product is >=2. The tail is
-- >=1 by the already proved certifiedModulusProductPositive.
nonemptyModulusProductHasAtLeastTwo :
  (axis : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  Σ Nat (λ a →
    Period.modulusProduct (axis ∷ rest) ≡ suc (suc a))
nonemptyModulusProductHasAtLeastTwo axis rest
  with axisHasAtLeastTwo axis
     | Lift.certifiedModulusProductPositive rest
... | c , axisPositive | b , tailPositive =
  (2 * b + c * suc b)
  ,
  trans
    (cong₂ _*_ axisPositive tailPositive)
    ((solve 2
      (λ c b →
        (con 2 :+ c) :* (con 1 :+ b)
        :=
        con 2 :+ ((con 2 :* b) :+ (c :* (con 1 :+ b))))
      refl) c b)

baselineAtLeastThree :
  (a : Nat) →
  baselineMinusOne (suc a)
    ≡ suc (suc (suc (2 * a)))
baselineAtLeastThree =
  solve 1
    (λ a →
      con 1 :+ (con 2 :* (con 1 :+ a))
      :=
      con 3 :+ (con 2 :* a))
    refl

-- UNCONDITIONAL in the input finite certified prime list: for every
-- nonempty list, the input baseline witness is constructed here.
-- The output n,n+2 satisfy the ACTUAL stdlib Composite predicates.
-- t ranges over all Nat, with the factor lift using suc t >=1.
everyNonemptyFinitePrimeSieveHasDoubleCompositeSurvivor :
  (axis : Pair.CertifiedPrimeAxis) →
  (rest : List Pair.CertifiedPrimeAxis) →
  (t : Nat) →
  Σ Nat (λ n →
    Pair.AllPairSurvive (axis ∷ rest) n
    × (Prime.Composite n × Prime.Composite (n + 2)))
everyNonemptyFinitePrimeSieveHasDoubleCompositeSurvivor axis rest t
  with nonemptyModulusProductHasAtLeastTwo axis rest
... | a , periodAtLeastTwo =
  Lift.factorableSurvivorWithBothCompositeCertificates
    (axis ∷ rest)
    (suc (2 * a))
    t
    (subst
      (Pair.AllPairSurvive (axis ∷ rest))
      (baselineAtLeastThree a)
      (baselineAllPairSurvivesAtCommonPeriod
        (axis ∷ rest) (suc a)
        (subst
          (Period.CommonPeriod (axis ∷ rest))
          periodAtLeastTwo
          (Period.productIsCommonPeriod (axis ∷ rest)))))
