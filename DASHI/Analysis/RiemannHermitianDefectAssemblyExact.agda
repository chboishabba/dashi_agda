module DASHI.Analysis.RiemannHermitianDefectAssemblyExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact terminal algebra for the complex-Poisson / Hermitian-energy route to
-- a transverse zeta-zero defect theorem.
--
-- Primary analytic calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- This module deliberately contains NO new analytic assertion about zeta.
-- Instead it proves, subtraction-free over Nat, the exact implication that the
-- remaining analytic producer must instantiate:
--
--   full-grid coercive defect
--       + finite-compression retention
--       + arithmetic transport
--       + vanishing arithmetic budget
--   ------------------------------------------------
--              weighted transverse defect = 0.
--
-- The equations are written with explicit nonnegative slack terms so that no
-- hidden subtraction or sign assumption is smuggled into the assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

sym : {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl yz = yz

------------------------------------------------------------------------
-- Elementary zero lemmas.
------------------------------------------------------------------------

sumZeroLeft : (a b : Nat) → a + b ≡ zero → a ≡ zero
sumZeroLeft zero b eq = refl
sumZeroLeft (suc a) b ()

sumZeroRight : (a b : Nat) → a + b ≡ zero → b ≡ zero
sumZeroRight a zero eq = refl
sumZeroRight a (suc b) ()

------------------------------------------------------------------------
-- Step 1 + Step 2 ledger.
------------------------------------------------------------------------

record FiniteHermitianRetention : Set where
  constructor finiteHermitianRetention
  field
    weightedTransverseDefect : Nat
    coercivitySlack : Nat
    fullGridExcess : Nat
    finiteCompressionExcess : Nat
    tailLoss : Nat
    retentionMargin : Nat

    fullGridCoercivity :
      weightedTransverseDefect + coercivitySlack ≡ fullGridExcess

    finiteTailDecomposition :
      fullGridExcess ≡ finiteCompressionExcess + tailLoss

    tailDominatedByFinite :
      tailLoss + retentionMargin ≡ finiteCompressionExcess

open FiniteHermitianRetention public

twoTimes : Nat → Nat
twoTimes n = n + n

finiteRetentionDominationIdentity :
  (r : FiniteHermitianRetention) →
  (weightedTransverseDefect r + coercivitySlack r) + retentionMargin r
    ≡ twoTimes (finiteCompressionExcess r)
finiteRetentionDominationIdentity r =
  let w = weightedTransverseDefect r
      c = coercivitySlack r
      f = finiteCompressionExcess r
      t = tailLoss r
      m = retentionMargin r
  in
  step w c f t m
    (fullGridCoercivity r)
    (finiteTailDecomposition r)
    (tailDominatedByFinite r)
  where
  step :
    (w c f t m : Nat) →
    w + c ≡ fullGridExcess r →
    fullGridExcess r ≡ f + t →
    t + m ≡ f →
    (w + c) + m ≡ f + f
  step w c f t m refl refl refl =
    solve 3
      (λ f t m → (f :+ t) :+ m := f :+ f)
      refl
      f t m

finiteZeroForcesTailZero :
  (r : FiniteHermitianRetention) →
  finiteCompressionExcess r ≡ zero →
  tailLoss r ≡ zero
finiteZeroForcesTailZero r hfinite =
  sumZeroLeft
    (tailLoss r)
    (retentionMargin r)
    (trans (tailDominatedByFinite r) hfinite)

finiteZeroForcesFullGridZero :
  (r : FiniteHermitianRetention) →
  finiteCompressionExcess r ≡ zero →
  fullGridExcess r ≡ zero
finiteZeroForcesFullGridZero r hfinite =
  trans
    (finiteTailDecomposition r)
    (zeroSum hfinite (finiteZeroForcesTailZero r hfinite))
  where
  zeroSum :
    finiteCompressionExcess r ≡ zero →
    tailLoss r ≡ zero →
    finiteCompressionExcess r + tailLoss r ≡ zero
  zeroSum refl refl = refl

finiteZeroForcesWeightedDefectZero :
  (r : FiniteHermitianRetention) →
  finiteCompressionExcess r ≡ zero →
  weightedTransverseDefect r ≡ zero
finiteZeroForcesWeightedDefectZero r hfinite =
  sumZeroLeft
    (weightedTransverseDefect r)
    (coercivitySlack r)
    (trans
      (fullGridCoercivity r)
      (finiteZeroForcesFullGridZero r hfinite))

------------------------------------------------------------------------
-- Step 3 ledger: transport the retained Hermitian excess to an arithmetic
-- observable without pretending the existing holomorphic Weil trace already
-- does this job.
------------------------------------------------------------------------

record HermitianArithmeticTransport : Set where
  constructor hermitianArithmeticTransport
  field
    retention : FiniteHermitianRetention
    arithmeticBudget : Nat
    transportRemainder : Nat
    arithmeticDecomposition :
      finiteCompressionExcess retention + transportRemainder ≡ arithmeticBudget

open HermitianArithmeticTransport public

zeroArithmeticBudgetForcesFiniteExcessZero :
  (a : HermitianArithmeticTransport) →
  arithmeticBudget a ≡ zero →
  finiteCompressionExcess (retention a) ≡ zero
zeroArithmeticBudgetForcesFiniteExcessZero a hbudget =
  sumZeroLeft
    (finiteCompressionExcess (retention a))
    (transportRemainder a)
    (trans (arithmeticDecomposition a) hbudget)

zeroArithmeticBudgetForcesWeightedDefectZero :
  (a : HermitianArithmeticTransport) →
  arithmeticBudget a ≡ zero →
  weightedTransverseDefect (retention a) ≡ zero
zeroArithmeticBudgetForcesWeightedDefectZero a hbudget =
  finiteZeroForcesWeightedDefectZero
    (retention a)
    (zeroArithmeticBudgetForcesFiniteExcessZero a hbudget)

------------------------------------------------------------------------
-- Step 4 / RH-facing socket.
------------------------------------------------------------------------

record HermitianDefectVanishingCriterion : Set₁ where
  field
    Zero : Set
    transverseDefect : Zero → Nat
    aggregateWeightedDefect : Nat
    aggregateZeroForcesPointwiseZero :
      aggregateWeightedDefect ≡ zero →
      (rho : Zero) → transverseDefect rho ≡ zero

record HermitianDreamAssembly : Set₁ where
  field
    transport : HermitianArithmeticTransport
    criterion : HermitianDefectVanishingCriterion
    aggregateIdentification :
      HermitianDefectVanishingCriterion.aggregateWeightedDefect criterion
        ≡ weightedTransverseDefect
            (retention transport)

aggregateDefectVanishesFromZeroArithmeticBudget :
  (a : HermitianDreamAssembly) →
  arithmeticBudget (HermitianDreamAssembly.transport a) ≡ zero →
  HermitianDefectVanishingCriterion.aggregateWeightedDefect
    (HermitianDreamAssembly.criterion a) ≡ zero
aggregateDefectVanishesFromZeroArithmeticBudget a hbudget =
  trans
    (HermitianDreamAssembly.aggregateIdentification a)
    (zeroArithmeticBudgetForcesWeightedDefectZero
      (HermitianDreamAssembly.transport a)
      hbudget)

pointwiseTransverseDefectVanishesFromZeroArithmeticBudget :
  (a : HermitianDreamAssembly) →
  arithmeticBudget (HermitianDreamAssembly.transport a) ≡ zero →
  (rho : HermitianDefectVanishingCriterion.Zero
    (HermitianDreamAssembly.criterion a)) →
  HermitianDefectVanishingCriterion.transverseDefect
    (HermitianDreamAssembly.criterion a) rho ≡ zero
pointwiseTransverseDefectVanishesFromZeroArithmeticBudget a hbudget =
  HermitianDefectVanishingCriterion.aggregateZeroForcesPointwiseZero
    (HermitianDreamAssembly.criterion a)
    (aggregateDefectVanishesFromZeroArithmeticBudget a hbudget)
