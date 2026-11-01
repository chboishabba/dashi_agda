module DASHI.Physics.Closure.NSTriadKNComIncidenceOffSupportRound46Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- DASHI CONTRIBUTION
--
-- Round 45 reduced the physical Com support theorem to two Bool branches.
-- Round 46 makes the zero branch combinatorial on the repository's literal
-- finite Fourier-triad enumeration.  A pair product is the nonnegative fold of
-- weights over the physical incidence list assigned to (q,r).  If the shell
-- support graph is inactive, the incidence list is exactly empty, hence the
-- pair product is definitionally zero after rewriting.
--
-- The only analytic branch left is the active finite incidence sum against the
-- six-three gap.  No operator-norm estimate is used to prove off-support zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Triad
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree
import DASHI.Physics.Closure.NSTriadKNComBooleanSupportActiveReductionRound45Exact as BoolSupport
import DASHI.Physics.Closure.NSTriadKNComSupportOverlapRound42Exact as Support

incidenceWeightSum :
  (Triad.PhysicalTriadIncidence → ℚ) →
  List Triad.PhysicalTriadIncidence → ℚ
incidenceWeightSum weight [] = 0ℚ
incidenceWeightSum weight (tau ∷ rest) =
  weight tau + incidenceWeightSum weight rest

record PhysicalComIncidenceSupportInput : Set where
  field
    cutoff : Nat
    shellDistance : Nat → Nat → Nat
    supportActive : Nat → Nat → Bool

    pairIncidences : Nat → Nat → List Triad.PhysicalTriadIncidence
    incidenceWeight : Triad.PhysicalTriadIncidence → ℚ
    incidenceWeightNonnegative : ∀ tau → 0ℚ ≤ incidenceWeight tau

    pairIncidencesArePhysical : ∀ q r tau →
      tau Cube.∈ pairIncidences q r →
      tau Cube.∈ Triad.physicalTriadEnumeration cutoff

    inactiveSupportHasEmptyIncidence : ∀ q r →
      supportActive q r ≡ false →
      pairIncidences q r ≡ []

    activeIncidenceSumBelowSixThree : ∀ q r →
      supportActive q r ≡ true →
      incidenceWeightSum incidenceWeight (pairIncidences q r)
      ≤ SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalComIncidenceSupportInput public

physicalIncidencePairProduct :
  PhysicalComIncidenceSupportInput → Nat → Nat → ℚ
physicalIncidencePairProduct physical q r =
  incidenceWeightSum
    (incidenceWeight physical)
    (pairIncidences physical q r)

incidenceWeightSumNonnegative :
  (physical : PhysicalComIncidenceSupportInput) →
  (cells : List Triad.PhysicalTriadIncidence) →
  0ℚ ≤ incidenceWeightSum (incidenceWeight physical) cells
incidenceWeightSumNonnegative physical [] = ℚP.≤-refl
incidenceWeightSumNonnegative physical (tau ∷ rest) =
  ℚP.+-mono-≤
    (incidenceWeightNonnegative physical tau)
    (incidenceWeightSumNonnegative physical rest)

physicalIncidencePairProductNonnegative :
  (physical : PhysicalComIncidenceSupportInput) →
  ∀ q r → 0ℚ ≤ physicalIncidencePairProduct physical q r
physicalIncidencePairProductNonnegative physical q r =
  incidenceWeightSumNonnegative physical (pairIncidences physical q r)

inactiveSupportAnnihilatesPhysicalIncidencePairProduct :
  (physical : PhysicalComIncidenceSupportInput) →
  ∀ q r →
  supportActive physical q r ≡ false →
  physicalIncidencePairProduct physical q r ≡ 0ℚ
inactiveSupportAnnihilatesPhysicalIncidencePairProduct physical q r inactive
  rewrite inactiveSupportHasEmptyIncidence physical q r inactive = refl

physicalIncidenceBooleanSupportInput :
  PhysicalComIncidenceSupportInput →
  BoolSupport.PhysicalOddPQBooleanSupportInput
physicalIncidenceBooleanSupportInput physical = record
  { physicalPairProduct = physicalIncidencePairProduct physical
  ; shellDistance = shellDistance physical
  ; supportActive = supportActive physical
  ; pairProductNonnegative =
      physicalIncidencePairProductNonnegative physical
  ; inactiveSupportAnnihilatesPairProduct =
      inactiveSupportAnnihilatesPhysicalIncidencePairProduct physical
  ; activeSupportPairProductBelowSixThree =
      activeIncidenceSumBelowSixThree physical
  }

physicalComEnvelopeFromIncidenceSupport :
  PhysicalComIncidenceSupportInput →
  Support.PhysicalComSupportOverlapEnvelope
physicalComEnvelopeFromIncidenceSupport physical =
  BoolSupport.physicalComBooleanSupportEnvelope
    (physicalIncidenceBooleanSupportInput physical)

comOffSupportReducedToEmptyPhysicalIncidence : Bool
comOffSupportReducedToEmptyPhysicalIncidence = true

comOffSupportReducedToEmptyPhysicalIncidenceIsTrue :
  comOffSupportReducedToEmptyPhysicalIncidence ≡ true
comOffSupportReducedToEmptyPhysicalIncidenceIsTrue = refl
