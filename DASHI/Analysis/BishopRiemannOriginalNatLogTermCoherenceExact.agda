module DASHI.Analysis.BishopRiemannOriginalNatLogTermCoherenceExact where

------------------------------------------------------------------------
-- Same-object Riemann Dirichlet term/limit transport between the
-- literal sourceNegativeLogValue Nat history and the original
-- configured Round11 negative-log sum. No second zeta function,
-- arbitrary equality-of-name record or generic real mirror.
--
-- The already-proved sourceOriginalConfiguredNatLogAgreement gives
-- the Nat-level logarithm equality. This module applies the ACTUAL
-- Bishop complex exp congruence to both original coordinates and
-- reuses the actual Bishop Dirichlet limit uniqueness, not a
-- Set-valued ZetaEqualsDirichletSeries field.
--
-- Not a P0 theorem: exp(-L_B)=1-x must still be proved for the
-- source region/Basel majorant. Does not claim analytic continuation.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)

import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Foundations.BishopNegativeLogGeometricSourceConvergenceExact as SourceLog
import DASHI.Analysis.BishopSetoidComplexExact as Complex
import DASHI.Analysis.BishopRiemannAnalyticSetoidExpReuseExact as ExpBridge
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopRiemannDirichletBaselSameObjectExact as Dirichlet
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Moonshine.BishopRound11MachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionRound11ExactCutset as Round11

-- Exact termwise source equality, not merely a comparison at one
-- exponent, and not classical equality of a new complex carrier.
originalDirichletExponentialRespectsNatLog :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (first second : Terms.NatLogCandidate) →
  ((n : Nat) → R._≃_ (first n) (second n)) →
  (s : BC.BishopComplex) →
  (n : Nat) →
  (R._≃_
    (BC.re (Terms.bishopDirichletExponentialTerm T first s n))
    (BC.re (Terms.bishopDirichletExponentialTerm T second s n)))
  ×
  (R._≃_
    (BC.im (Terms.bishopDirichletExponentialTerm T first s n))
    (BC.im (Terms.bishopDirichletExponentialTerm T second s n)))
originalDirichletExponentialRespectsNatLog T first second logSame s n =
  ExpBridge.bishopAnalyticExpCongruent T
    (RP.*-cong RP.≃-refl (logSame n))
    (RP.*-cong RP.≃-refl (logSame n))

-- No additional abstract "same log" parameter: the supplied
-- configuration and literal original coefficient identification
-- are precisely the preexisting concrete source owners.
configuredRound11TermsAreCanonical :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (inside : (n : Nat) →
    Elementary.InOpenUnitInterval
      (Complex.dataSet T) (Terms.natLogArgument n)) →
  ((n index : Nat) →
    R._≃_
      (Elementary.negativeLogOneMinusTerm
        (Complex.dataSet T) (Terms.natLogArgument n) index)
      (SourceLog.sourceNegativeLogTerm
        (Terms.natLogArgument n) index)) →
  (s : BC.BishopComplex) →
  (n : Nat) →
  (R._≃_
    (BC.re (Terms.bishopDirichletExponentialTerm T
      (Terms.natLogViaOriginalNegativeLog T inside) s n))
    (BC.re (Terms.bishopDirichletExponentialTerm T
      Terms.sourceCanonicalNatLogCandidate s n)))
  ×
  (R._≃_
    (BC.im (Terms.bishopDirichletExponentialTerm T
      (Terms.natLogViaOriginalNegativeLog T inside) s n))
    (BC.im (Terms.bishopDirichletExponentialTerm T
      Terms.sourceCanonicalNatLogCandidate s n)))
configuredRound11TermsAreCanonical T inside coefficientsAgree s n =
  originalDirichletExponentialRespectsNatLog
    T
    (Terms.natLogViaOriginalNegativeLog T inside)
    Terms.sourceCanonicalNatLogCandidate
    (Terms.sourceOriginalConfiguredNatLogAgreement
      T inside coefficientsAgree)
    s n

-- The corresponding Bishop SERIES limits are the same, regardless
-- of which original Nat-log presentation is used. Both limits must
-- have their own authentic Basel majorant: no arbitrary function
-- equality is smuggled into the hypotheses.
originalDirichletLimitsRespectNatLog :
  (T : Complex.BishopSetoidComplexTranscendentals) →
  (first second : Terms.NatLogCandidate) →
  ((n : Nat) → R._≃_ (first n) (second n)) →
  (s : BC.BishopComplex) →
  (firstBound : Dirichlet.BishopDirichletBaselMajorantAt
    (Terms.bishopDirichletExponentialTerm T first) s) →
  (secondBound : Dirichlet.BishopDirichletBaselMajorantAt
    (Terms.bishopDirichletExponentialTerm T second) s) →
  (R._≃_
    (BC.re (Dirichlet.dirichletValue
      (Terms.bishopDirichletExponentialTerm T first) s firstBound))
    (BC.re (Dirichlet.dirichletValue
      (Terms.bishopDirichletExponentialTerm T second) s secondBound)))
  ×
  (R._≃_
    (BC.im (Dirichlet.dirichletValue
      (Terms.bishopDirichletExponentialTerm T first) s firstBound))
    (BC.im (Dirichlet.dirichletValue
      (Terms.bishopDirichletExponentialTerm T second) s secondBound)))
originalDirichletLimitsRespectNatLog
    T first second logSame s firstBound secondBound =
  Dirichlet.dirichletValuesRespectTermwiseEquality
    (Terms.bishopDirichletExponentialTerm T first)
    (Terms.bishopDirichletExponentialTerm T second)
    s firstBound secondBound
    (λ n → proj₁
      (originalDirichletExponentialRespectsNatLog
        T first second logSame s n))
    (λ n → proj₂
      (originalDirichletExponentialRespectsNatLog
        T first second logSame s n))
