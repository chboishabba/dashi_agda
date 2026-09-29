{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicProductionSwapInvariantRound758Exact where

------------------------------------------------------------------------
-- ROUND758 / THE R748 DYADIC PRODUCTION CORRECTION IS P/Q-SWAP INVARIANT
--
-- orderedPairPower is the ordered cell plus its physical p/q partner, hence it
-- is exactly invariant under swap.  R119 proves that the p- and q-energy legs
-- exchange under the same swap.  Since the selected dyadic weights on p and q
-- exchange as well, the complete paired production orbit is pointwise
-- swap-invariant.
--
-- Under the ordinary reality/divergence-free hypotheses used by R748, both
-- sides reduce to the two-difference normal form.  Therefore
--
--   PairedTwoDifference(swap beta) = PairedTwoDifference(beta).
--
-- This removes the production correction as a possible source of LH/HL
-- asymmetry.  Any failure of the FULL R749 residual cell to be swap invariant
-- must come from the nested-orbit term.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact as R119
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact as R748

F : C3.RealField _
F = Rational.rationalRealField

orderedPairPowerSwapInvariant :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  R38.orderedPairPower E I (Symmetry.swapTriad tau) velocity
  ≡ R38.orderedPairPower E I tau velocity
orderedPairPowerSwapInvariant {E} {I} tau velocity =
  let
    a = R38.orderedPower E I tau velocity
    b = R38.orderedPower E I (Symmetry.swapTriad tau) velocity
  in
  trans
    (R38.orderedPairPowerIsOrderedPlusSwap
      E I (Symmetry.swapTriad tau) velocity)
    (trans
      (cong₂ _+_
        refl
        (cong
          (λ selected → R38.orderedPower E I selected velocity)
          (R38.swapTriadInvolutiveExact tau)))
      (trans
        (solve (a ∷ b ∷ []))
        (sym
          (R38.orderedPairPowerIsOrderedPlusSwap E I tau velocity))))

pairedProductionOrbitSwapInvariant :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  R748.pairedProductionOrbitCell system (Symmetry.swapTriad tau)
  ≡ R748.pairedProductionOrbitCell system tau
pairedProductionOrbitSwapInvariant {E} {I} system tau =
  let
    velocity = Audit.velocity system

    pk =
      R38.orderedPairPower E I tau velocity
    pp =
      R38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
    pq =
      R38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity

    wk = R748.selectedDyadicWeight (Physical.k tau)
    wp = R748.selectedDyadicWeight (Physical.p tau)
    wq = R748.selectedDyadicWeight (Physical.q tau)

    kPair :
      R38.orderedPairPower E I (Symmetry.swapTriad tau) velocity
      ≡ pk
    kPair = orderedPairPowerSwapInvariant tau velocity

    pPair :
      R38.orderedPairPower E I
        (Orbit.pEnergyLeg (Symmetry.swapTriad tau)) velocity
      ≡ pq
    pPair =
      cong
        (λ selected → R38.orderedPairPower E I selected velocity)
        (R119.pEnergyLegSwapIsQEnergyLeg tau)

    qPair :
      R38.orderedPairPower E I
        (Orbit.qEnergyLeg (Symmetry.swapTriad tau)) velocity
      ≡ pp
    qPair =
      cong
        (λ selected → R38.orderedPairPower E I selected velocity)
        (R119.qEnergyLegSwapIsPEnergyLeg tau)
  in
  rewrite Symmetry.swapTriadK tau
        | Symmetry.swapTriadP tau
        | Symmetry.swapTriadQ tau
        | kPair
        | pPair
        | qPair =
    solve (wk ∷ wp ∷ wq ∷ pk ∷ pp ∷ pq ∷ [])

pairedTwoDifferenceSwapInvariant :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  (tau : Physical.PhysicalTriadIncidence) →
  R748.pairedProductionTwoDifferenceCell system (Symmetry.swapTriad tau)
  ≡ R748.pairedProductionTwoDifferenceCell system tau
pairedTwoDifferenceSwapInvariant
    system reality divergenceFree tau =
  trans
    (sym
      (R748.pairedProductionOrbitIsTwoDifferences
        system reality divergenceFree (Symmetry.swapTriad tau)))
    (trans
      (pairedProductionOrbitSwapInvariant system tau)
      (R748.pairedProductionOrbitIsTwoDifferences
        system reality divergenceFree tau))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round758OrderedPairPowerSwapInvariant : Bool
round758OrderedPairPowerSwapInvariant = true

round758PairedProductionOrbitSwapInvariant : Bool
round758PairedProductionOrbitSwapInvariant = true

round758TwoDifferenceProductionSwapInvariant : Bool
round758TwoDifferenceProductionSwapInvariant = true

round758ProductionCausesLHHLAsymmetry : Bool
round758ProductionCausesLHHLAsymmetry = false

round758NestedOrbitSwapInvariantProvedHere : Bool
round758NestedOrbitSwapInvariantProvedHere = false

round758IntroducesEstimate : Bool
round758IntroducesEstimate = false

round758ClayPromotion : Bool
round758ClayPromotion = false

round758OrderedPairPowerSwapInvariantIsTrue :
  round758OrderedPairPowerSwapInvariant ≡ true
round758OrderedPairPowerSwapInvariantIsTrue = refl

round758PairedProductionOrbitSwapInvariantIsTrue :
  round758PairedProductionOrbitSwapInvariant ≡ true
round758PairedProductionOrbitSwapInvariantIsTrue = refl

round758TwoDifferenceProductionSwapInvariantIsTrue :
  round758TwoDifferenceProductionSwapInvariant ≡ true
round758TwoDifferenceProductionSwapInvariantIsTrue = refl

round758ProductionCausesLHHLAsymmetryIsFalse :
  round758ProductionCausesLHHLAsymmetry ≡ false
round758ProductionCausesLHHLAsymmetryIsFalse = refl

round758NestedOrbitSwapInvariantProvedHereIsFalse :
  round758NestedOrbitSwapInvariantProvedHere ≡ false
round758NestedOrbitSwapInvariantProvedHereIsFalse = refl

round758IntroducesEstimateIsFalse :
  round758IntroducesEstimate ≡ false
round758IntroducesEstimateIsFalse = refl

round758ClayPromotionIsFalse :
  round758ClayPromotion ≡ false
round758ClayPromotionIsFalse = refl
