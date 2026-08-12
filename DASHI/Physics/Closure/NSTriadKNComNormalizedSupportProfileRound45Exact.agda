module DASHI.Physics.Closure.NSTriadKNComNormalizedSupportProfileRound45Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Proceedings of the Symposium on Ergodic Theory, 1955.
-- DOI: no DOI assigned to the cited historical conference article.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 42/43 already reduced Com to one literal pair-product inequality
--
--   P(q,r) <= m(q,r) g_6,3(distance(q,r)),   0 <= m <= 1.
--
-- The useful normalized quantity is therefore not an independently fitted
-- scalar and need not be defined by division.  The support multiplicity itself
-- is the certified dimensionless profile.  This file names that profile and
-- proves its complete normalization contract directly from the physical input:
--
--   0 <= M(q,r) <= 1,
--   P(q,r) <= M(q,r) g_6,3(distance(q,r)).
--
-- For the Bool specialization this profile is literally the 0/1 support
-- witness constructed from the projection graph.  The only remaining Com PDE
-- theorem is therefore the actual physical product domination supplying the
-- Round-43 input; no extra normalization theorem is owed afterwards.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNComAdjointSupportEnvelopeRound43Exact as Adjoint

physicalComNormalizedProfile :
  Adjoint.PhysicalOddPQAdjointSupportInput → Nat → Nat → ℚ
physicalComNormalizedProfile physical =
  Adjoint.supportMultiplicity physical

physicalComNormalizedProfileNonnegative :
  (physical : Adjoint.PhysicalOddPQAdjointSupportInput) →
  ∀ q r → 0ℚ ≤ physicalComNormalizedProfile physical q r
physicalComNormalizedProfileNonnegative physical =
  Adjoint.supportMultiplicityNonnegative physical

physicalComNormalizedProfileAtMostOne :
  (physical : Adjoint.PhysicalOddPQAdjointSupportInput) →
  ∀ q r → physicalComNormalizedProfile physical q r ≤ 1ℚ
physicalComNormalizedProfileAtMostOne physical =
  Adjoint.supportMultiplicityAtMostOne physical

physicalPairProductBelowNormalizedProfileTimesGap :
  (physical : Adjoint.PhysicalOddPQAdjointSupportInput) →
  ∀ q r →
  Adjoint.physicalPairProduct physical q r
  ≤ physicalComNormalizedProfile physical q r
      * SixThree.twoBranchSquaredGap
          (Adjoint.shellDistance physical q r)
physicalPairProductBelowNormalizedProfileTimesGap physical =
  Adjoint.physicalOddPQFirstProductBelowSupportTimesSixThree physical

physicalPairProductBelowUnitSixThreeGap :
  (physical : Adjoint.PhysicalOddPQAdjointSupportInput) →
  ∀ q r →
  Adjoint.physicalPairProduct physical q r
  ≤ SixThree.twoBranchSquaredGap
      (Adjoint.shellDistance physical q r)
physicalPairProductBelowUnitSixThreeGap physical =
  Support.physicalProductBelowSixThree
    (Adjoint.physicalOddPQSupportEnvelope physical)

boolComNormalizedProfile : Bool → ℚ
boolComNormalizedProfile = Support.boolSupportMultiplicity

boolComNormalizedProfileNonnegative :
  ∀ support → 0ℚ ≤ boolComNormalizedProfile support
boolComNormalizedProfileNonnegative =
  Support.boolSupportMultiplicityNonnegative

boolComNormalizedProfileAtMostOne :
  ∀ support → boolComNormalizedProfile support ≤ 1ℚ
boolComNormalizedProfileAtMostOne =
  Support.boolSupportMultiplicityAtMostOne

comNormalizedProfileIsLiteralSupportWitness : Bool
comNormalizedProfileIsLiteralSupportWitness = true

comNormalizedProfileIsLiteralSupportWitnessIsTrue :
  comNormalizedProfileIsLiteralSupportWitness ≡ true
comNormalizedProfileIsLiteralSupportWitnessIsTrue = refl
