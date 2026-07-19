module DASHI.Analysis.RiemannZetaProgramBoundary where

-- The repository currently carries exact rational samples at s = 0 and
-- s = -1.  This module makes the missing analytic ladder explicit, so those
-- samples cannot be promoted into a Riemann-zeta or Riemann-Hypothesis claim.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Q using (ℚ)
open import DASHI.Analysis.AbelZeta as Abel
open import DASHI.Analysis.ThreeAdicGeometricSeries as ThreeAdic

------------------------------------------------------------------------
-- Exact sample layer
------------------------------------------------------------------------

record ExactZetaSamples : Set where
  field
    zetaAtZero : ℚ
    zetaAtMinusOne : ℚ
    zetaAtZeroMatchesAbel : zetaAtZero ≡ Abel.zeta0
    zetaAtMinusOneMatchesAbel : zetaAtMinusOne ≡ Abel.zetaMinus1

exactZetaSamples : ExactZetaSamples
exactZetaSamples = record
  { zetaAtZero = Abel.zeta0
  ; zetaAtMinusOne = Abel.zetaMinus1
  ; zetaAtZeroMatchesAbel = refl
  ; zetaAtMinusOneMatchesAbel = refl
  }

------------------------------------------------------------------------
-- Missing analytic ladder
------------------------------------------------------------------------

record DirichletHalfPlaneWitness : Set₁ where
  field
    Complex : Set
    zeta : Complex → Complex
    realPartGreaterThanOne : Complex → Set
    dirichletSeriesConverges : (s : Complex) → realPartGreaterThanOne s → Set
    zetaEqualsDirichletSeries : (s : Complex) → realPartGreaterThanOne s → Set

record EulerProductWitness : Set₁ where
  field
    Complex : Set
    zeta : Complex → Complex
    realPartGreaterThanOne : Complex → Set
    eulerProductConverges : (s : Complex) → realPartGreaterThanOne s → Set
    zetaEqualsEulerProduct : (s : Complex) → realPartGreaterThanOne s → Set

record MeromorphicContinuationWitness : Set₁ where
  field
    Complex : Set
    continuedZeta : Complex → Complex
    one : Complex
    meromorphicAwayFromOne : Set
    simplePoleAtOne : Set

record FunctionalEquationWitness : Set₁ where
  field
    Complex : Set
    completedZeta : Complex → Complex
    oneMinus : Complex → Complex
    functionalEquation : (s : Complex) → completedZeta s ≡ completedZeta (oneMinus s)

record CriticalStripWitness : Set₁ where
  field
    Complex : Set
    zeta : Complex → Complex
    zero : Complex
    realPart : Complex → ℚ
    oneHalf : ℚ
    nontrivialZero : Complex → Set
    criticalLine : Complex → Set
    criticalLineMeansHalf : (s : Complex) → criticalLine s → realPart s ≡ oneHalf

record RiemannHypothesisWitness : Set₁ where
  field
    strip : CriticalStripWitness
    everyNontrivialZeroOnCriticalLine :
      (s : CriticalStripWitness.Complex strip) →
      CriticalStripWitness.nontrivialZero strip s →
      CriticalStripWitness.criticalLine strip s

------------------------------------------------------------------------
-- Fail-closed promotion gate
------------------------------------------------------------------------

record RiemannZetaProgram : Set₁ where
  field
    exactSamples : ExactZetaSamples
    dirichletHalfPlane : DirichletHalfPlaneWitness
    eulerProduct : EulerProductWitness
    meromorphicContinuation : MeromorphicContinuationWitness
    functionalEquation : FunctionalEquationWitness
    criticalStrip : CriticalStripWitness
    riemannHypothesis : RiemannHypothesisWitness

-- There is intentionally no constructor for RiemannZetaProgram in this
-- module.  The exact samples do not discharge any of the analytic fields.

record CurrentZetaBoundary : Set where
  field
    exactSamplesAvailable : ⊤
    threeAdicMinusHalfIsSeparate : ⊤
    dirichletHalfPlaneNotDischarged : ⊤
    eulerProductNotDischarged : ⊤
    meromorphicContinuationNotDischarged : ⊤
    functionalEquationNotDischarged : ⊤
    criticalStripNotDischarged : ⊤
    riemannHypothesisNotDischarged : ⊤
    noZeroFinderClaim : ⊤
    noCriticalLineSamplingClaim : ⊤

currentZetaBoundary : CurrentZetaBoundary
currentZetaBoundary = record
  { exactSamplesAvailable = tt
  ; threeAdicMinusHalfIsSeparate = tt
  ; dirichletHalfPlaneNotDischarged = tt
  ; eulerProductNotDischarged = tt
  ; meromorphicContinuationNotDischarged = tt
  ; functionalEquationNotDischarged = tt
  ; criticalStripNotDischarged = tt
  ; riemannHypothesisNotDischarged = tt
  ; noZeroFinderClaim = tt
  ; noCriticalLineSamplingClaim = tt
  }

record ZetaThreeAdicSeparationReceipt : Set where
  field
    zetaZeroValue : ℚ
    threeAdicGeometricValue : ℚ
    valuesCoincide : zetaZeroValue ≡ threeAdicGeometricValue
    mechanismsAreDistinct : ⊤
    zetaMechanism : String
    threeAdicMechanism : String

zetaThreeAdicSeparationReceipt : ZetaThreeAdicSeparationReceipt
zetaThreeAdicSeparationReceipt = record
  { zetaZeroValue = Abel.zeta0
  ; threeAdicGeometricValue = ThreeAdic.minusHalf
  ; valuesCoincide = refl
  ; mechanismsAreDistinct = tt
  ; zetaMechanism = "eta-to-zeta continuation value at s = 0"
  ; threeAdicMechanism = "3-adic limit of finite geometric partial sums"
  }
