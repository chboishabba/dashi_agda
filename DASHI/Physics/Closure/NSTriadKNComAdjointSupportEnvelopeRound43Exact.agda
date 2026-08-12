module DASHI.Physics.Closure.NSTriadKNComAdjointSupportEnvelopeRound43Exact where

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
-- Round 40 already proved the literal physical transport matrix is
-- skew-adjoint entrywise.  Consequently the two Cotlar faces of the odd P/Q
-- channel are not independent analytic inputs.  Round 42's support-overlap
-- envelope still stored two pair-product functions plus a separate equality.
--
-- This file removes that duplication.  A physical input owns one literal
-- one-channel pair product, one shell distance and one support multiplicity.
-- Both Cotlar faces are definitionally this same scalar product.  Hence
-- pairProductsCoincide is refl; the only nontrivial physical estimate left is
--
--   physicalPairProduct(q,r)
--     <= supportMultiplicity(q,r) * sixThreeGap(distance(q,r)).
--
-- This is the exact architectural consequence of the already-proved T*=-T
-- seam: no second Gram estimate may be requested merely because Cotlar writes
-- two adjoint products.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact as Bridge
import DASHI.Physics.Closure.NSTriadKNPhysicalTransportMatrixSkewRound40Exact as Skew

record PhysicalOddPQAdjointSupportInput : Set where
  field
    physicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat
    supportMultiplicity : Nat → Nat → ℚ

    pairProductNonnegative : ∀ q r →
      0ℚ ≤ physicalPairProduct q r

    supportMultiplicityNonnegative : ∀ q r →
      0ℚ ≤ supportMultiplicity q r

    supportMultiplicityAtMostOne : ∀ q r →
      supportMultiplicity q r ≤ 1ℚ

    physicalOddPQFirstProductBelowSupportTimesSixThree : ∀ q r →
      physicalPairProduct q r
      ≤ supportMultiplicity q r
          * SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalOddPQAdjointSupportInput public

physicalOddPQSupportEnvelope :
  PhysicalOddPQAdjointSupportInput →
  Support.PhysicalComSupportOverlapEnvelope
physicalOddPQSupportEnvelope physical = record
  { firstPhysicalPairProduct = physicalPairProduct physical
  ; secondPhysicalPairProduct = physicalPairProduct physical
  ; shellDistance = shellDistance physical
  ; supportMultiplicity = supportMultiplicity physical
  ; pairProductsCoincide = λ q r → refl
  ; firstProductNonnegative = pairProductNonnegative physical
  ; supportMultiplicityNonnegative = supportMultiplicityNonnegative physical
  ; supportMultiplicityAtMostOne = supportMultiplicityAtMostOne physical
  ; firstProductBelowSupportTimesSixThree =
      physicalOddPQFirstProductBelowSupportTimesSixThree physical
  }

physicalOddPQFirstPairDecay :
  (physical : PhysicalOddPQAdjointSupportInput) →
  ∀ q r →
  physicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
physicalOddPQFirstPairDecay physical =
  Support.supportOverlapFirstPhysicalPairDecay
    (physicalOddPQSupportEnvelope physical)

physicalOddPQSecondPairDecay :
  (physical : PhysicalOddPQAdjointSupportInput) →
  ∀ q r →
  physicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
physicalOddPQSecondPairDecay physical =
  Support.supportOverlapSecondPhysicalPairDecay
    (physicalOddPQSupportEnvelope physical)

physicalTransportSkewAdjointAlreadyConstructed : Bool
physicalTransportSkewAdjointAlreadyConstructed =
  Skew.physicalLowTransportGlobalMatrixSkewAdjointPointwiseConstructed

comAdjointFaceDuplicationRemoved : Bool
comAdjointFaceDuplicationRemoved = true

physicalComNowReducedToOneSupportProductBound : Bool
physicalComNowReducedToOneSupportProductBound = true

comAdjointFaceDuplicationRemovedIsTrue :
  comAdjointFaceDuplicationRemoved ≡ true
comAdjointFaceDuplicationRemovedIsTrue = refl

physicalComNowReducedToOneSupportProductBoundIsTrue :
  physicalComNowReducedToOneSupportProductBound ≡ true
physicalComNowReducedToOneSupportProductBoundIsTrue = refl
