module DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact where

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
-- The Round-42 support theorem is most physical when its multiplicity is the
-- literal Bool overlap graph.  Then the weighted inequality
--
--   P(q,r) <= 1_overlap(q,r) * g_6,3(distance(q,r))
--
-- is exactly equivalent to two support-local statements:
--
--   overlap=false  => P(q,r)=0,
--   overlap=true   => P(q,r)<=g_6,3(distance(q,r)).
--
-- This file proves the forward construction needed by the closure lane.  It
-- removes any temptation to invent a fractional fitting multiplicity: the
-- remaining PDE work is now (i) literal off-support annihilation by the shell
-- projectors and (ii) the active-channel six-three estimate.  Together they
-- construct the existing Round-43 one-channel support input and hence both
-- Cotlar faces.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support
import DASHI.Physics.Closure.NSTriadKNComAdjointSupportEnvelopeRound43Exact as Adjoint

record PhysicalOddPQBooleanSupportInput : Set where
  field
    physicalPairProduct : Nat → Nat → ℚ
    shellDistance : Nat → Nat → Nat
    supportActive : Nat → Nat → Bool

    pairProductNonnegative : ∀ q r →
      0ℚ ≤ physicalPairProduct q r

    inactiveSupportAnnihilatesPairProduct : ∀ q r →
      supportActive q r ≡ false →
      physicalPairProduct q r ≡ 0ℚ

    activeSupportPairProductBelowSixThree : ∀ q r →
      supportActive q r ≡ true →
      physicalPairProduct q r
      ≤ SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalOddPQBooleanSupportInput public

pairProductBelowBooleanSupportTimesSixThree :
  (physical : PhysicalOddPQBooleanSupportInput) →
  ∀ q r →
  physicalPairProduct physical q r
  ≤ Support.boolSupportMultiplicity (supportActive physical q r)
      * SixThree.twoBranchSquaredGap (shellDistance physical q r)
pairProductBelowBooleanSupportTimesSixThree physical q r
  with supportActive physical q r
... | false =
  let
    zeroProduct : physicalPairProduct physical q r ≡ 0ℚ
    zeroProduct = inactiveSupportAnnihilatesPairProduct physical q r refl

    rightMeaning :
      Support.boolSupportMultiplicity false
        * SixThree.twoBranchSquaredGap (shellDistance physical q r)
      ≡ 0ℚ
    rightMeaning = solve
      (SixThree.twoBranchSquaredGap (shellDistance physical q r) ∷ [])
  in
  subst
    (λ lower →
      lower
      ≤ Support.boolSupportMultiplicity false
          * SixThree.twoBranchSquaredGap (shellDistance physical q r))
    (sym zeroProduct)
    (subst
      (λ upper → 0ℚ ≤ upper)
      (sym rightMeaning)
      ℚP.≤-refl)
... | true =
  let
    active = activeSupportPairProductBelowSixThree physical q r refl
    rightMeaning :
      Support.boolSupportMultiplicity true
        * SixThree.twoBranchSquaredGap (shellDistance physical q r)
      ≡ SixThree.twoBranchSquaredGap (shellDistance physical q r)
    rightMeaning = solve
      (SixThree.twoBranchSquaredGap (shellDistance physical q r) ∷ [])
  in
  subst
    (λ upper →
      physicalPairProduct physical q r ≤ upper)
    (sym rightMeaning)
    active

asRound43OddPQSupportInput :
  PhysicalOddPQBooleanSupportInput →
  Adjoint.PhysicalOddPQAdjointSupportInput
asRound43OddPQSupportInput physical = record
  { physicalPairProduct = physicalPairProduct physical
  ; shellDistance = shellDistance physical
  ; supportMultiplicity = λ q r →
      Support.boolSupportMultiplicity (supportActive physical q r)
  ; pairProductNonnegative = pairProductNonnegative physical
  ; supportMultiplicityNonnegative = λ q r →
      Support.boolSupportMultiplicityNonnegative (supportActive physical q r)
  ; supportMultiplicityAtMostOne = λ q r →
      Support.boolSupportMultiplicityAtMostOne (supportActive physical q r)
  ; physicalOddPQFirstProductBelowSupportTimesSixThree =
      pairProductBelowBooleanSupportTimesSixThree physical
  }

physicalComBooleanSupportEnvelope :
  PhysicalOddPQBooleanSupportInput →
  Support.PhysicalComSupportOverlapEnvelope
physicalComBooleanSupportEnvelope physical =
  Adjoint.physicalOddPQSupportEnvelope (asRound43OddPQSupportInput physical)

comBooleanSupportReducedToInactiveZeroAndActiveGap : Bool
comBooleanSupportReducedToInactiveZeroAndActiveGap = true

comBooleanSupportReducedToInactiveZeroAndActiveGapIsTrue :
  comBooleanSupportReducedToInactiveZeroAndActiveGap ≡ true
comBooleanSupportReducedToInactiveZeroAndActiveGapIsTrue = refl
