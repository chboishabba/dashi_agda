module DASHI.Physics.Closure.NSTriadKNComActiveSixThreeRealizationRound61Exact where

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
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- ROUND 61 CONTRIBUTION
--
-- Round60's lightweight B source still accepted the desired 17/64 and 65/512
-- inequalities as three fields.  That is stronger than the genuine physical
-- frontier and duplicates arithmetic already proved in Round35/47.
--
-- IMPORTANT CORRECTION TO THE FIRST ROUND61 DRAFT
--
-- Round35 explicitly describes `sixThreeGramCell` as a SCALE-ENVELOPE
-- candidate.  It is not the literal Fourier Gram and should not be equated to
-- the physical T_q^*T_r / T_qT_r^* pair product.  The honest B frontier is the
-- two-step statement already suggested by the Round35 architecture:
--
--   (B1) on an active literal odd-(P/Q) fibre, identify the normalized pair
--        product EXACTLY with the pair product of an actual physical
--        `GramInterferenceCell`;
--
--   (B3) prove that this physical cell's overlap is bounded by the existing
--        six-three two-branch scale envelope.
--
-- Outer contractions then remove the two physical outer factors, giving
--
--   normalized pair product
--     <= physical overlap
--     <= sixThree twoBranchSquaredGap(shellDistance).
--
-- Common-hat width one reduces active fibres to distances 0 and 1, where the
-- existing exact arithmetic is
--
--   g_6,3(0) = 17/64,
--   g_6,3(1) = 65/512.
--
-- The Round60 aggregate therefore still gives the full 133/256 endpoint, but
-- without the false/over-strong claim that the literal physical Gram itself is
-- definitionally the six-three model cell.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNComCommonHatSupportLeafRound58 as Hat
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreMassLeafRound58 as LightGram
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreSourceRound60Exact as Source
import DASHI.Physics.Closure.NSTriadKNComNormalizedFibreAggregateRound60Exact as Aggregate
import DASHI.Physics.Closure.NSTriadKNComGramInterferenceRound35Exact as Gram
import DASHI.Physics.Closure.NSTriadKNComSameAdjacentActiveRound47Exact as Legacy
import DASHI.Physics.Closure.NSTriadKNComDyadicHatWidthOneRound46Exact as HatWidth
import DASHI.Physics.Closure.NSTriadKNLuoSixThreeCenteredCommutatorScaleExact as SixThree

record PhysicalActiveSixThreeOddPQSource : Set₁ where
  field
    support : Hat.PhysicalOddPQCommonHatIdentification

    -- This is the normalized squared physical T* T / T T* fibre mass, not a
    -- raw velocity-linear transport coefficient.
    normalizedPairProduct : Nat → Nat → ℚ
    normalizedPairProductNonnegative : ∀ q r →
      0ℚ ≤ normalizedPairProduct q r

    shellDistance : Nat → Nat → Nat
    sameShellDistance : ∀ q → shellDistance q q ≡ zero
    forwardAdjacentDistance : ∀ q →
      shellDistance q (suc q) ≡ suc zero
    reverseAdjacentDistance : ∀ q →
      shellDistance (suc q) q ≡ suc zero

    inactivePairProductZero : ∀ q r →
      Hat.supportActive support q r ≡ false →
      normalizedPairProduct q r ≡ 0ℚ

    -- B1: exact same-object identification to the ACTUAL physical factorized
    -- Gram cell.  The active proof is indexed so no off-support model value is
    -- introduced.
    activePhysicalGramCell : ∀ q r →
      Hat.supportActive support q r ≡ true →
      Gram.GramInterferenceCell (shellDistance q r)

    activeProductIsPhysicalGram : ∀ q r →
      (active : Hat.supportActive support q r ≡ true) →
      normalizedPairProduct q r
      ≡ Gram.pairProduct (activePhysicalGramCell q r active)

    -- B3 analytic heart: only the overlap is compared to the six-three scale
    -- envelope.  Outer contractions are already theorem-level Round35 data.
    activePhysicalOverlapBelowSixThree : ∀ q r →
      (active : Hat.supportActive support q r ≡ true) →
      Gram.overlap (activePhysicalGramCell q r active)
      ≤ SixThree.twoBranchSquaredGap (shellDistance q r)

open PhysicalActiveSixThreeOddPQSource public

asNormalizedRealization :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  LightGram.PhysicalNormalizedOddPQGramRealization (support physical)
asNormalizedRealization physical = record
  { normalizedSquaredGramEnergy = normalizedPairProduct physical
  ; normalizedSquaredGramEnergyNonnegative =
      normalizedPairProductNonnegative physical
  }

activeWithinOne :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q r → Hat.supportActive (support physical) q r ≡ true →
  HatWidth.WithinOne q r
activeWithinOne physical = Hat.commonHatWidthOne (support physical)

activePairProductBelowSixThree :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q r →
  (active : Hat.supportActive (support physical) q r ≡ true) →
  normalizedPairProduct physical q r
  ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r)
activePairProductBelowSixThree physical q r active =
  let
    cell = activePhysicalGramCell physical q r active
    gramToOverlap :
      Gram.pairProduct cell ≤ Gram.overlap cell
    gramToOverlap = Gram.outerContractionsRemove cell

    gramToSixThree :
      Gram.pairProduct cell
      ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r)
    gramToSixThree =
      ℚP.≤-trans
        gramToOverlap
        (activePhysicalOverlapBelowSixThree physical q r active)
  in
  subst
    (λ lower →
      lower ≤ SixThree.twoBranchSquaredGap (shellDistance physical q r))
    (sym (activeProductIsPhysicalGram physical q r active))
    gramToSixThree

sameShellBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) q q ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) q q
  ≤ LightGram.sameShellTarget
sameShellBoundDerived physical q active
  rewrite sameShellDistance physical q
        | Legacy.sixThreeSameShellExact =
  activePairProductBelowSixThree physical q q active

forwardAdjacentBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) q (suc q) ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) q (suc q)
  ≤ LightGram.adjacentShellTarget
forwardAdjacentBoundDerived physical q active
  rewrite forwardAdjacentDistance physical q
        | Legacy.sixThreeAdjacentShellExact =
  activePairProductBelowSixThree physical q (suc q) active

reverseAdjacentBoundDerived :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Hat.supportActive (support physical) (suc q) q ≡ true →
  LightGram.pairProduct (asNormalizedRealization physical) (suc q) q
  ≤ LightGram.adjacentShellTarget
reverseAdjacentBoundDerived physical q active
  rewrite reverseAdjacentDistance physical q
        | Legacy.sixThreeAdjacentShellExact =
  activePairProductBelowSixThree physical (suc q) q active

asSameAdjacentBounds :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  LightGram.SameAdjacentNormalizedFibreMassBounds
    (asNormalizedRealization physical)
asSameAdjacentBounds physical = record
  { sameShellBound = sameShellBoundDerived physical
  ; forwardAdjacentBound = forwardAdjacentBoundDerived physical
  ; reverseAdjacentBound = reverseAdjacentBoundDerived physical
  }

asPhysicalNormalizedOddPQSource :
  PhysicalActiveSixThreeOddPQSource → Source.PhysicalNormalizedOddPQSource
asPhysicalNormalizedOddPQSource physical = record
  { support = support physical
  ; realization = asNormalizedRealization physical
  ; bounds = asSameAdjacentBounds physical
  ; shellDistance = shellDistance physical
  ; sameShellDistance = sameShellDistance physical
  ; forwardAdjacentDistance = forwardAdjacentDistance physical
  ; reverseAdjacentDistance = reverseAdjacentDistance physical
  ; inactiveSupportAnnihilatesPairProduct = inactivePairProductZero physical
  }

fullBandwidthOneMassBelow133Over256 :
  (physical : PhysicalActiveSixThreeOddPQSource) →
  ∀ q →
  Aggregate.normalizedOddPQBandwidthOneMass
    (asPhysicalNormalizedOddPQSource physical) q
  ≤ Aggregate.bandwidthOneTarget
fullBandwidthOneMassBelow133Over256 physical =
  Aggregate.normalizedOddPQBandwidthOneMassBelow133Over256
    (asPhysicalNormalizedOddPQSource physical)

b1ExactPhysicalGramThenB3SixThreeOverlapSuffices : Bool
b1ExactPhysicalGramThenB3SixThreeOverlapSuffices = true

b1ExactPhysicalGramThenB3SixThreeOverlapSufficesIsTrue :
  b1ExactPhysicalGramThenB3SixThreeOverlapSuffices ≡ true
b1ExactPhysicalGramThenB3SixThreeOverlapSufficesIsTrue = refl
