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
--
-- `weightedTransverseDefect` stands for a quantity such as
--
--   c_phi * alpha^2
--
-- or an aggregate sum of such terms.
--
-- `coercivitySlack` records how much larger the full-grid Hermitian excess is
-- than that coercive lower target:
--
--   weightedDefect + coercivitySlack = fullGridExcess.
--
-- `tailLoss` is the Hermitian energy omitted by the finite k-window:
--
--   fullGridExcess = finiteCompressionExcess + tailLoss.
--
-- `retentionMargin` certifies that the retained finite excess dominates the
-- tail loss:
--
--   tailLoss + retentionMargin = finiteCompressionExcess.
--
-- Together these imply the exact domination identity
--
--   weightedDefect + coercivitySlack + retentionMargin
--      = 2 * finiteCompressionExcess.
--
-- Hence the familiar inequality weightedDefect <= 2 finiteExcess is recovered
-- without introducing an order API.
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

finiteZeroForcesWeightedDefectZero :
  (r : FiniteHermitianRetention) →
  finiteCompressionExcess r ≡ zero →
  weightedTransverseDefect r ≡ zero
finiteZeroForcesWeightedDefectZero r hfinite =
  sumZeroLeft
    (weightedTransverseDefect r)
    (coercivitySlack r)
    (transFull r)
  where
  transFull :
    (q : FiniteHermitianRetention) →
    weightedTransverseDefect q + coercivitySlack q ≡ zero
  transFull q rewrite fullGridCoercivity q | finiteTailDecomposition q | hfinite =
    sumZeroLeft zero (tailLoss q) refl

------------------------------------------------------------------------
-- Step 3 ledger: transport the retained Hermitian excess to an arithmetic
-- observable without pretending the existing holomorphic Weil trace already
-- does this job.
--
-- The nonnegative `transportRemainder` makes the desired domination exact:
--
--   finite Hermitian excess + remainder = arithmetic budget.
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
    eq0
  where
  eq0 :
    finiteCompressionExcess (retention a) + transportRemainder a ≡ zero
  eq0 rewrite arithmeticDecomposition a | hbudget = refl

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
--
-- This record does not identify `Zero` with actual zeta zeros.  It states the
-- final logical interface required once the analytic substrate supplies a
-- weighted defect whose vanishing forces each transverse displacement to
-- vanish.
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
aggregateDefectVanishesFromZeroArithmeticBudget a hbudget rewrite
  HermitianDreamAssembly.aggregateIdentification a =
    zeroArithmeticBudgetForcesWeightedDefectZero
      (HermitianDreamAssembly.transport a)
      hbudget

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
