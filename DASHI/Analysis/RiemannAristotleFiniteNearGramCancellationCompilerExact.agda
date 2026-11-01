module DASHI.Analysis.RiemannAristotleFiniteNearGramCancellationCompilerExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ; _+_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Analysis.RiemannAristotleFiniteNearCoreSchurCompilerExact as Near

------------------------------------------------------------------------
-- FINITE POST-SCHUR GRAM LEDGER
--
-- After the explicit cutoff theorem, the difficult carrier is finite.  If its
-- post-Schur orbit contributions are v_i, then the exact energy identity is
--
--   ||sum_i v_i||^2
--     = sum_i ||v_i||^2 + 2 sum_{i<j} <v_i,v_j>.
--
-- The second term is kept SIGNED.  This is the whole point of the compiler:
-- replacing it by a sum of absolute covariances would throw away the finite
-- cancellation that S2 still needs.
--
-- Agda does not reconstruct the zeta vectors here.  The domain owner supplies
-- the exact identity on the literal finite post-Schur carrier.
------------------------------------------------------------------------

record FiniteNearGramLedger : Set where
  constructor finite-near-gram-ledger
  field
    cutoff : Nat

    nearSchurSq : ℚ
    diagonalMass : ℚ
    twiceCrossMass : ℚ

    exactGramIdentity :
      nearSchurSq ≡ diagonalMass + twiceCrossMass

    diagonalBudget : ℚ
    twiceCrossBudget : ℚ

    diagonalBound : diagonalMass ≤ diagonalBudget
    signedCrossBound : twiceCrossMass ≤ twiceCrossBudget

open FiniteNearGramLedger public

nearSchurBound :
  (d : FiniteNearGramLedger) →
  nearSchurSq d ≤ diagonalBudget d + twiceCrossBudget d
nearSchurBound d =
  subst
    (λ x → x ≤ diagonalBudget d + twiceCrossBudget d)
    (sym (exactGramIdentity d))
    (ℚP.+-mono-≤ (diagonalBound d) (signedCrossBound d))
  where
    open import Relation.Binary.PropositionalEquality using (subst; sym)

------------------------------------------------------------------------
-- Direct bridge to the already-owned finite-near + explicit-far perturbation
-- consumer.  The far error remains a mechanical explicit-cutoff payment.
------------------------------------------------------------------------

record FiniteNearGramWithFarAllowance : Set where
  constructor finite-near-gram-with-far-allowance
  field
    gram : FiniteNearGramLedger

    offSchurSq farErrorSq farAllowance clusterMargin : ℚ

    perturbationBound :
      offSchurSq
        ≤ ((+ 2 / 1) * FiniteNearGramLedger.nearSchurSq gram)
          + ((+ 2 / 1) * farErrorSq)

    farErrorBound : farErrorSq ≤ farAllowance

    weightedActualsBelowAllowances :
      ((+ 2 / 1) * FiniteNearGramLedger.nearSchurSq gram)
        + ((+ 2 / 1) * farErrorSq)
      ≤
      ((+ 2 / 1) *
        (FiniteNearGramLedger.diagonalBudget gram
          + FiniteNearGramLedger.twiceCrossBudget gram))
        + ((+ 2 / 1) * farAllowance)

    finalGramAllowanceBelowCluster :
      ((+ 2 / 1) *
        (FiniteNearGramLedger.diagonalBudget gram
          + FiniteNearGramLedger.twiceCrossBudget gram))
        + ((+ 2 / 1) * farAllowance)
      < clusterMargin

open FiniteNearGramWithFarAllowance public

compiledFiniteNearPerturbation :
  (d : FiniteNearGramWithFarAllowance) → Near.FiniteNearCoreSchurPerturbation
compiledFiniteNearPerturbation d =
  record
    { cutoff = FiniteNearGramLedger.cutoff (gram d)
    ; offSchurSq = offSchurSq d
    ; nearSchurSq = FiniteNearGramLedger.nearSchurSq (gram d)
    ; farErrorSq = farErrorSq d
    ; clusterMargin = clusterMargin d
    ; perturbationBound = perturbationBound d
    ; finiteNearPlusFarBelowCluster =
        ℚP.≤-<-trans
          (weightedActualsBelowAllowances d)
          (finalGramAllowanceBelowCluster d)
    }

finiteNearGramContradictsExactSchur :
  (d : FiniteNearGramWithFarAllowance) →
  clusterMargin d ≡ offSchurSq d →
  ⊥
finiteNearGramContradictsExactSchur d exactSchur =
  Near.finiteNearCoreContradictsExactSchur
    (compiledFiniteNearPerturbation d)
    exactSchur

------------------------------------------------------------------------
-- Research boundary.
------------------------------------------------------------------------

record FiniteNearGramBoundary : Set where
  constructor finite-near-gram-boundary
  field
    exactFiniteGramCompilerClosed : Bool
    exactFiniteGramCompilerClosedIsTrue : exactFiniteGramCompilerClosed ≡ true

    crossTermKeptSigned : Bool
    crossTermKeptSignedIsTrue : crossTermKeptSigned ≡ true

    absoluteCrossMajorantAcceptedAsCompletion : Bool
    absoluteCrossMajorantAcceptedAsCompletionIsFalse :
      absoluteCrossMajorantAcceptedAsCompletion ≡ false

    literalFiniteNearGramIdentityInstantiated : Bool
    literalFiniteNearGramIdentityInstantiatedIsFalse :
      literalFiniteNearGramIdentityInstantiated ≡ false

    signedFiniteCrossTermEstimateClosed : Bool
    signedFiniteCrossTermEstimateClosedIsFalse :
      signedFiniteCrossTermEstimateClosed ≡ false

canonicalFiniteNearGramBoundary : FiniteNearGramBoundary
canonicalFiniteNearGramBoundary =
  finite-near-gram-boundary true refl true refl false refl false refl false refl
