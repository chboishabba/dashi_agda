module DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- Communications on Pure and Applied Mathematics 41 (1988), 891--907.
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
-- Round 41 reduced the physical Com theorem to one cross-channel Gram face,
-- but the provisional same-object route still asked for the exact equality
--
--   physical pair product = six-three Gram pair product.
--
-- The attached analysis suggested a sharper route: use shell-support
-- intersection before norm estimation.  This file proves that exact equality
-- is stronger than necessary.
--
-- Let m(q,r) be a nonnegative support-overlap multiplicity with m<=1.  If the
-- literal one-channel physical pair product obeys
--
--   P(q,r) <= m(q,r) * g(|q-r|),
--
-- where g is the already-certified centered (L6,L3) two-branch squared gap,
-- then automatically
--
--   P(q,r) <= g(|q-r|) <= (1/2) 2^{-|q-r|}.
--
-- We construct an actual Round-35 `GramInterferenceCell` whose pairProduct is
-- the literal physical P(q,r), whose overlap is g, and whose outer factors are
-- exactly one.  Therefore the Round-40 single-channel realization follows
-- without identifying P itself with the model Gram value.
--
-- A Bool support graph is supplied as the canonical 0/1 specialization.  The
-- remaining physical Com theorem is now the concrete support/product bound on
-- U_q^* U_r (plus the already-proved adjoint-face equality), not an artificial
-- exact numerical equality with the six-three candidate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComCotlarDyadicEnvelopeRound34Exact as Cotlar
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeComCotlarBridgeRound34Exact as Bridge
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComSingleGramReductionRound40Exact as Single

boolSupportMultiplicity : Bool → ℚ
boolSupportMultiplicity true = 1ℚ
boolSupportMultiplicity false = 0ℚ

boolSupportMultiplicityNonnegative :
  ∀ support → 0ℚ ≤ boolSupportMultiplicity support
boolSupportMultiplicityNonnegative true = ℚP.0≤1
boolSupportMultiplicityNonnegative false = ℚP.≤-refl

boolSupportMultiplicityAtMostOne :
  ∀ support → boolSupportMultiplicity support ≤ 1ℚ
boolSupportMultiplicityAtMostOne true = ℚP.≤-refl
boolSupportMultiplicityAtMostOne false = ℚP.0≤1

record PhysicalComSupportOverlapEnvelope : Set where
  field
    firstPhysicalPairProduct : Nat → Nat → ℚ
    secondPhysicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat
    supportMultiplicity : Nat → Nat → ℚ

    pairProductsCoincide : ∀ q r →
      firstPhysicalPairProduct q r ≡ secondPhysicalPairProduct q r

    firstProductNonnegative : ∀ q r →
      0ℚ ≤ firstPhysicalPairProduct q r

    supportMultiplicityNonnegative : ∀ q r →
      0ℚ ≤ supportMultiplicity q r

    supportMultiplicityAtMostOne : ∀ q r →
      supportMultiplicity q r ≤ 1ℚ

    firstProductBelowSupportTimesSixThree : ∀ q r →
      firstPhysicalPairProduct q r
      ≤ supportMultiplicity q r
          * SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalComSupportOverlapEnvelope public

supportTimesSixThreeBelowSixThree :
  (physical : PhysicalComSupportOverlapEnvelope) →
  ∀ q r →
  supportMultiplicity physical q r
      * SixThree.twoBranchSquaredGap (shellDistance physical q r)
  ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r)
supportTimesSixThreeBelowSixThree physical q r =
  let
    gap = shellDistance physical q r
    gapNN = Gram.sixThreeOverlapNonnegative gap

    scaled :
      supportMultiplicity physical q r * SixThree.twoBranchSquaredGap gap
      ≤ 1ℚ * SixThree.twoBranchSquaredGap gap
    scaled =
      let instance gapNNI = nonNegative gapNN
      in ℚP.*-monoʳ-≤-nonNeg
        (SixThree.twoBranchSquaredGap gap)
        (supportMultiplicityAtMostOne physical q r)
  in
  subst
    (λ upper →
      supportMultiplicity physical q r * SixThree.twoBranchSquaredGap gap
      ≤ upper)
    (ℚP.*-identityˡ (SixThree.twoBranchSquaredGap gap))
    scaled

physicalProductBelowSixThree :
  (physical : PhysicalComSupportOverlapEnvelope) →
  ∀ q r →
  firstPhysicalPairProduct physical q r
  ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r)
physicalProductBelowSixThree physical q r =
  ℚP.≤-trans
    (firstProductBelowSupportTimesSixThree physical q r)
    (supportTimesSixThreeBelowSixThree physical q r)

supportGramCell :
  (physical : PhysicalComSupportOverlapEnvelope) →
  (q r : Nat) →
  Gram.GramInterferenceCell (shellDistance physical q r)
supportGramCell physical q r =
  Gram.gram-interference-cell
    1ℚ
    (SixThree.twoBranchSquaredGap gap)
    1ℚ
    (firstPhysicalPairProduct physical q r)
    ℚP.0≤1
    (Gram.sixThreeOverlapNonnegative gap)
    ℚP.0≤1
    (firstProductNonnegative physical q r)
    ℚP.≤-refl
    ℚP.≤-refl
    factorizationBound
  where
  gap = shellDistance physical q r

  factorizationBound :
    firstPhysicalPairProduct physical q r
    ≤ 1ℚ * SixThree.twoBranchSquaredGap gap * 1ℚ
  factorizationBound =
    let
      endpoint :
        1ℚ * SixThree.twoBranchSquaredGap gap * 1ℚ
        ≡ SixThree.twoBranchSquaredGap gap
      endpoint = solve (SixThree.twoBranchSquaredGap gap ∷ [])
    in
    subst
      (λ upper → firstPhysicalPairProduct physical q r ≤ upper)
      (sym endpoint)
      (physicalProductBelowSixThree physical q r)

singleChannelGramFromSupportOverlap :
  PhysicalComSupportOverlapEnvelope →
  Single.PhysicalComSingleChannelGramRealization
singleChannelGramFromSupportOverlap physical = record
  { firstPhysicalPairProduct = firstPhysicalPairProduct physical
  ; secondPhysicalPairProduct = secondPhysicalPairProduct physical
  ; shellDistance = shellDistance physical
  ; pairProductsCoincide = pairProductsCoincide physical
  ; singleGram = supportGramCell physical
  ; firstProductExact = λ q r → refl
  ; singleOverlapHalfDyadic = λ q r →
      Bridge.sixThreeSquaredGapFitsCotlarHalf
        (shellDistance physical q r)
  }

supportOverlapFirstPhysicalPairDecay :
  (physical : PhysicalComSupportOverlapEnvelope) →
  ∀ q r →
  firstPhysicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
supportOverlapFirstPhysicalPairDecay physical =
  Single.singleChannelFirstPairDecay
    (singleChannelGramFromSupportOverlap physical)

supportOverlapSecondPhysicalPairDecay :
  (physical : PhysicalComSupportOverlapEnvelope) →
  ∀ q r →
  secondPhysicalPairProduct physical q r
  ≤ Cotlar.directEnvelope Bridge.half (shellDistance physical q r)
supportOverlapSecondPhysicalPairDecay physical =
  Single.singleChannelSecondPairDecay
    (singleChannelGramFromSupportOverlap physical)

record PhysicalComBooleanSupportEnvelope : Set where
  field
    firstPhysicalPairProduct : Nat → Nat → ℚ
    secondPhysicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat
    supportActive : Nat → Nat → Bool
    pairProductsCoincide : ∀ q r →
      firstPhysicalPairProduct q r ≡ secondPhysicalPairProduct q r
    firstProductNonnegative : ∀ q r →
      0ℚ ≤ firstPhysicalPairProduct q r
    firstProductBelowActiveSixThree : ∀ q r →
      firstPhysicalPairProduct q r
      ≤ boolSupportMultiplicity (supportActive q r)
          * SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalComBooleanSupportEnvelope public

supportEnvelopeFromBooleanGraph :
  PhysicalComBooleanSupportEnvelope → PhysicalComSupportOverlapEnvelope
supportEnvelopeFromBooleanGraph physical = record
  { firstPhysicalPairProduct = firstPhysicalPairProduct physical
  ; secondPhysicalPairProduct = secondPhysicalPairProduct physical
  ; shellDistance = shellDistance physical
  ; supportMultiplicity = λ q r → boolSupportMultiplicity (supportActive physical q r)
  ; pairProductsCoincide = pairProductsCoincide physical
  ; firstProductNonnegative = firstProductNonnegative physical
  ; supportMultiplicityNonnegative = λ q r →
      boolSupportMultiplicityNonnegative (supportActive physical q r)
  ; supportMultiplicityAtMostOne = λ q r →
      boolSupportMultiplicityAtMostOne (supportActive physical q r)
  ; firstProductBelowSupportTimesSixThree =
      firstProductBelowActiveSixThree physical
  }

comSupportOverlapReductionClosed : Bool
comSupportOverlapReductionClosed = true

comBooleanSupportGraphReductionClosed : Bool
comBooleanSupportGraphReductionClosed = true

physicalOddPQSupportEnvelopeConstructed : Bool
physicalOddPQSupportEnvelopeConstructed = false

comSupportOverlapReductionClosedIsTrue :
  comSupportOverlapReductionClosed ≡ true
comSupportOverlapReductionClosedIsTrue = refl

comBooleanSupportGraphReductionClosedIsTrue :
  comBooleanSupportGraphReductionClosed ≡ true
comBooleanSupportGraphReductionClosedIsTrue = refl
