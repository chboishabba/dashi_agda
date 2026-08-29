module DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact where

------------------------------------------------------------------------
-- BIDI MEETING POINT AFTER THE EXPLICIT D_off CUTOFF THEOREM
--
-- Lean now proves, taper-by-taper, that the literal off-ordinate projective
-- defect differs from a FINITE signed near-core sum by an explicit far error.
--
-- For the three-taper RH observer the remaining analytic theorem should be
-- stated after deterministic Schur elimination, not as a raw absolute zero-mass
-- estimate.  If
--
--   X = E D_off,
--   N = E D_near(J),
--   F = E (D_off - D_near(J)),
--
-- then X = N + F.  A standard quadratic perturbation estimate has shape
--
--   ||X||^2 <= 2 ||N||^2 + 2 ||F||^2.
--
-- This file owns the scalar compiler consuming that estimate.  The domain
-- producer remains responsible for instantiating `nearSchurSq` with the actual
-- finite signed nearOffFinset vector and `farErrorSq` with the literal explicit
-- cutoff remainder transported through the Schur contraction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

record FiniteNearCoreSchurPerturbation : Set where
  constructor finite-near-core-schur-perturbation
  field
    cutoff : Nat

    offSchurSq : ℚ
    nearSchurSq : ℚ
    farErrorSq : ℚ
    clusterMargin : ℚ

    -- Domain/vector owner: X = N + F followed by the Hilbert-space inequality
    -- ||N+F||^2 <= 2||N||^2 + 2||F||^2.
    perturbationBound :
      offSchurSq ≤ ((+ 2 / 1) * nearSchurSq) + ((+ 2 / 1) * farErrorSq)

    -- This is now the exact finite research payment.
    finiteNearPlusFarBelowCluster :
      ((+ 2 / 1) * nearSchurSq) + ((+ 2 / 1) * farErrorSq) < clusterMargin

open FiniteNearCoreSchurPerturbation public

offSchurStrictlyBelowCluster :
  (d : FiniteNearCoreSchurPerturbation) →
  offSchurSq d < clusterMargin d
offSchurStrictlyBelowCluster d =
  ℚP.≤-<-trans (perturbationBound d) (finiteNearPlusFarBelowCluster d)

finiteNearCoreContradictsExactSchur :
  (d : FiniteNearCoreSchurPerturbation) →
  clusterMargin d ≡ offSchurSq d →
  ⊥
finiteNearCoreContradictsExactSchur d exactSchur =
  ℚP.<-irrefl refl
    (subst (λ x → x < clusterMargin d)
      (sym exactSchur)
      (offSchurStrictlyBelowCluster d))
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- A more producer-friendly allowance form.
--
-- Instead of proving the final weighted sum directly, the finite near-core
-- analysis may expose separate allowances for its Schur energy and the explicit
-- far error.
------------------------------------------------------------------------

record FiniteNearCoreAllowance : Set where
  constructor finite-near-core-allowance
  field
    cutoff : Nat
    nearSchurSq farErrorSq nearAllowance farAllowance clusterMargin : ℚ

    nearBound : nearSchurSq ≤ nearAllowance
    farBound : farErrorSq ≤ farAllowance

    weightedAllowancesBelowCluster :
      ((+ 2 / 1) * nearAllowance) + ((+ 2 / 1) * farAllowance) < clusterMargin

open FiniteNearCoreAllowance public

weightedActualsBelowCluster :
  (d : FiniteNearCoreAllowance) →
  ((+ 2 / 1) * nearSchurSq d) + ((+ 2 / 1) * farErrorSq d)
    < clusterMargin d
weightedActualsBelowCluster d =
  ℚP.≤-<-trans
    (ℚP.+-mono-≤
      (ℚP.*-monoˡ-≤ (nearBound d) (record { numerator = 2 ; denominator = 1 ; isCoprime = _ }))
      (ℚP.*-monoˡ-≤ (farBound d) (record { numerator = 2 ; denominator = 1 ; isCoprime = _ })))
    (weightedAllowancesBelowCluster d)

------------------------------------------------------------------------
-- Status boundary.
------------------------------------------------------------------------

record FiniteNearCoreSchurBoundary : Set where
  constructor finite-near-core-schur-boundary
  field
    literalFiniteNearCarrierClosedInLean : Bool
    literalFiniteNearCarrierClosedInLeanIsTrue :
      literalFiniteNearCarrierClosedInLean ≡ true

    explicitFarRemainderClosedInLean : Bool
    explicitFarRemainderClosedInLeanIsTrue :
      explicitFarRemainderClosedInLean ≡ true

    scalarPerturbationConsumerClosedInAgda : Bool
    scalarPerturbationConsumerClosedInAgdaIsTrue :
      scalarPerturbationConsumerClosedInAgda ≡ true

    finiteNearSchurCancellationClosed : Bool
    finiteNearSchurCancellationClosedIsFalse :
      finiteNearSchurCancellationClosed ≡ false

canonicalFiniteNearCoreSchurBoundary : FiniteNearCoreSchurBoundary
canonicalFiniteNearCoreSchurBoundary =
  finite-near-core-schur-boundary true refl true refl true refl false refl
