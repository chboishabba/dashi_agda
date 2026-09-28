{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650DyadicPairedProductionDifferenceRound748Exact where

------------------------------------------------------------------------
-- ROUND748 / PAIR THE R744 PRODUCTION ORBIT, THEN USE THREE-LEG ENERGY
--
-- A single oriented R38 orderedPower does not satisfy the physical three-leg
-- energy cancellation termwise.  The exact local cancellation is carried by
-- orderedPairPower = orderedPower(tau) + orderedPower(swap tau).
--
-- Define the zero-safe dyadic coefficient
--
--   lambda~(m) = 0                  if m = 0
--              = dyadicWeight(m)   otherwise.
--
-- Then on one physical incidence:
--
--   PairOrbit(tau)
--     = lambda~(k) PairPower(tau)
--       + lambda~(p) PairPower(pLeg tau)
--       + lambda~(q) PairPower(qLeg tau)
--
-- and physical three-leg energy cancellation gives exactly
--
--   PairOrbit(tau)
--     = (lambda~(k)-lambda~(q)) PairPower(tau)
--       + (lambda~(p)-lambda~(q)) PairPower(pLeg tau).
--
-- Globally, swap/p/q are permutations of the complete physical enumeration,
-- so
--
--   sum PairOrbit = 2 * sum R744.productionOrbitCell.
--
-- Thus the actual dyadic critical production has a literal two-difference
-- local normal form after the necessary swap pairing, with no radial-weight
-- substitution and no estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxComplementRound98Exact as R98C
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact as R744

F : C3.RealField _
F = Rational.rationalRealField

selectedDyadicWeight : Z3.FourierMode → ℚ
selectedDyadicWeight mode with Output.modeEqual mode Z3.zeroMode
... | true = 0ℚ
... | false = Fold.dyadicCriticalWeight mode

selectedWeightAtK :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  selectedDyadicWeight (Physical.k tau)
    * R38.orderedPower E I tau (Audit.velocity system)
  ≡ R744.maskedProductionCell system tau
selectedWeightAtK system tau
  with Output.modeEqual (Physical.k tau) Z3.zeroMode
... | true = solve []
... | false = refl

pairedWeightedCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → ℚ
pairedWeightedCell {E} {I} system tau =
  selectedDyadicWeight (Physical.k tau)
    * R38.orderedPairPower E I tau (Audit.velocity system)

pairedWeightedCellIsOrderedPlusSwap :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (tau : Physical.PhysicalTriadIncidence) →
  pairedWeightedCell system tau
  ≡
  R744.maskedProductionCell system tau
    + R744.maskedProductionCell system (Symmetry.swapTriad tau)
pairedWeightedCellIsOrderedPlusSwap {E} {I} system tau =
  let
    weight = selectedDyadicWeight (Physical.k tau)
    ordered = R38.orderedPower E I tau (Audit.velocity system)
    swapped =
      R38.orderedPower E I (Symmetry.swapTriad tau) (Audit.velocity system)

    expandPair :
      pairedWeightedCell system tau
      ≡ weight * ordered + weight * swapped
    expandPair =
      trans
        (cong
          (weight *_)
          (R38.orderedPairPowerIsOrderedPlusSwap
            E I tau (Audit.velocity system)))
        (solve (weight ∷ ordered ∷ swapped ∷ []))

    firstMeaning :
      weight * ordered ≡ R744.maskedProductionCell system tau
    firstMeaning = selectedWeightAtK system tau

    swapWeightMeaning :
      selectedDyadicWeight (Physical.k (Symmetry.swapTriad tau))
      ≡ weight
    swapWeightMeaning
      rewrite Symmetry.swapTriadK tau = refl

    secondMeaning :
      weight * swapped
      ≡ R744.maskedProductionCell system (Symmetry.swapTriad tau)
    secondMeaning =
      trans
        (cong
          (_* swapped)
          (sym swapWeightMeaning))
        (selectedWeightAtK system (Symmetry.swapTriad tau))
  in
  trans expandPair
    (cong₂ _+_ firstMeaning secondMeaning)

pairedProductionOrbitCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → ℚ
pairedProductionOrbitCell {E} {I} system tau =
  let velocity = Audit.velocity system in
  selectedDyadicWeight (Physical.k tau)
      * R38.orderedPairPower E I tau velocity
    + selectedDyadicWeight (Physical.p tau)
      * R38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
    + selectedDyadicWeight (Physical.q tau)
      * R38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity

pairedProductionTwoDifferenceCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → ℚ
pairedProductionTwoDifferenceCell {E} {I} system tau =
  let
    velocity = Audit.velocity system
    pk = R38.orderedPairPower E I tau velocity
    pp = R38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
  in
  ( selectedDyadicWeight (Physical.k tau)
      - selectedDyadicWeight (Physical.q tau) ) * pk
  +
  ( selectedDyadicWeight (Physical.p tau)
      - selectedDyadicWeight (Physical.q tau) ) * pp

pairedProductionOrbitIsTwoDifferences :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Reality.RealityCondition (Audit.velocity system) →
  Reality.DivergenceFreeCondition E (Audit.velocity system) →
  (tau : Physical.PhysicalTriadIncidence) →
  pairedProductionOrbitCell system tau
  ≡ pairedProductionTwoDifferenceCell system tau
pairedProductionOrbitIsTwoDifferences {E} {I}
    system reality divergenceFree tau =
  let
    velocity = Audit.velocity system
    pk = R38.orderedPairPower E I tau velocity
    pp = R38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
    pq = R38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity
    wk = selectedDyadicWeight (Physical.k tau)
    wp = selectedDyadicWeight (Physical.p tau)
    wq = selectedDyadicWeight (Physical.q tau)

    energyZero : pk + pp + pq ≡ 0ℚ
    energyZero =
      R98C.threeLegOrderedPowerZero
        E I velocity reality divergenceFree tau

    eliminateQ : pq ≡ - (pk + pp)
    eliminateQ =
      let shifted = cong (λ value → value - (pk + pp)) energyZero
      in
      trans
        (solve (pk ∷ pp ∷ pq ∷ []))
        (trans shifted (solve (pk ∷ pp ∷ [])))
  in
  rewrite eliminateQ =
    solve (wk ∷ wp ∷ wq ∷ pk ∷ pp ∷ [])

foldPairedWeightedIsDoubleMasked :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  R38.foldPower (pairedWeightedCell system)
    (Physical.physicalTriadEnumeration (Audit.cutoff system))
  ≡
  Fold.two *
    R38.foldPower (R744.maskedProductionCell system)
      (Physical.physicalTriadEnumeration (Audit.cutoff system))
foldPairedWeightedIsDoubleMasked system =
  let
    items = Physical.physicalTriadEnumeration (Audit.cutoff system)
    base =
      R38.foldPower (R744.maskedProductionCell system) items

    split :
      R38.foldPower (pairedWeightedCell system) items
      ≡
      base
      + R38.foldPower
          (λ tau →
            R744.maskedProductionCell system (Symmetry.swapTriad tau))
          items
    split = go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower (pairedWeightedCell system) xs
        ≡
        R38.foldPower (R744.maskedProductionCell system) xs
        +
        R38.foldPower
          (λ tau →
            R744.maskedProductionCell system (Symmetry.swapTriad tau))
          xs
      go [] = solve []
      go (tau ∷ rest) =
        trans
          (cong₂ _+_
            (pairedWeightedCellIsOrderedPlusSwap system tau)
            (go rest))
          (solve
            ( R744.maskedProductionCell system tau
            ∷ R744.maskedProductionCell system (Symmetry.swapTriad tau)
            ∷ R38.foldPower (R744.maskedProductionCell system) rest
            ∷ R38.foldPower
                (λ selected →
                  R744.maskedProductionCell system
                    (Symmetry.swapTriad selected))
                rest
            ∷ []))

    swapInvariant :
      R38.foldPower
        (λ tau →
          R744.maskedProductionCell system (Symmetry.swapTriad tau))
        items
      ≡ base
    swapInvariant =
      trans
        (sym
          (R38.foldMap
            (R744.maskedProductionCell system)
            Symmetry.swapTriad items))
        (R38.foldPermutationInvariant
          (R744.maskedProductionCell system)
          (R38.swapTriadEnumerationPermutation (Audit.cutoff system)))
  in
  trans split
    (trans
      (cong (base +_) swapInvariant)
      (solve (base ∷ Fold.two ∷ [])))

foldPairedProductionOrbit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  R38.foldPower (pairedProductionOrbitCell system)
    (Physical.physicalTriadEnumeration (Audit.cutoff system))
  ≡
  Fold.two *
    R38.foldPower (R744.productionOrbitCell system)
      (Physical.physicalTriadEnumeration (Audit.cutoff system))
foldPairedProductionOrbit system =
  let
    items = Physical.physicalTriadEnumeration (Audit.cutoff system)
    pairBase = R38.foldPower (pairedWeightedCell system) items
    maskedBase =
      R38.foldPower (R744.maskedProductionCell system) items

    splitOrbit :
      R38.foldPower (pairedProductionOrbitCell system) items
      ≡ pairBase + pairBase + pairBase
    splitOrbit =
      let
        rawSplit :
          R38.foldPower (pairedProductionOrbitCell system) items
          ≡
          R38.foldPower (pairedWeightedCell system) items
          +
          R38.foldPower
            (λ tau → pairedWeightedCell system (Orbit.pEnergyLeg tau))
            items
          +
          R38.foldPower
            (λ tau → pairedWeightedCell system (Orbit.qEnergyLeg tau))
            items
        rawSplit = go items
          where
          go :
            (xs : List Physical.PhysicalTriadIncidence) →
            R38.foldPower (pairedProductionOrbitCell system) xs
            ≡
            R38.foldPower (pairedWeightedCell system) xs
            +
            R38.foldPower
              (λ tau → pairedWeightedCell system (Orbit.pEnergyLeg tau))
              xs
            +
            R38.foldPower
              (λ tau → pairedWeightedCell system (Orbit.qEnergyLeg tau))
              xs
          go [] = solve []
          go (tau ∷ rest) =
            trans
              (cong
                (pairedProductionOrbitCell system tau +_)
                (go rest))
              (solve
                ( pairedWeightedCell system tau
                ∷ pairedWeightedCell system (Orbit.pEnergyLeg tau)
                ∷ pairedWeightedCell system (Orbit.qEnergyLeg tau)
                ∷ R38.foldPower (pairedWeightedCell system) rest
                ∷ R38.foldPower
                    (λ selected →
                      pairedWeightedCell system (Orbit.pEnergyLeg selected))
                    rest
                ∷ R38.foldPower
                    (λ selected →
                      pairedWeightedCell system (Orbit.qEnergyLeg selected))
                    rest
                ∷ []))

        pInvariant :
          R38.foldPower
            (λ tau → pairedWeightedCell system (Orbit.pEnergyLeg tau))
            items
          ≡ pairBase
        pInvariant =
          trans
            (sym
              (R38.foldMap
                (pairedWeightedCell system) Orbit.pEnergyLeg items))
            (R38.foldPermutationInvariant
              (pairedWeightedCell system)
              (R38.pEnergyLegEnumerationPermutation (Audit.cutoff system)))

        qInvariant :
          R38.foldPower
            (λ tau → pairedWeightedCell system (Orbit.qEnergyLeg tau))
            items
          ≡ pairBase
        qInvariant =
          trans
            (sym
              (R38.foldMap
                (pairedWeightedCell system) Orbit.qEnergyLeg items))
            (R38.foldPermutationInvariant
              (pairedWeightedCell system)
              (R38.qEnergyLegEnumerationPermutation (Audit.cutoff system)))
      in
      trans rawSplit
        (cong₂ _+_ refl (cong₂ _+_ pInvariant qInvariant))

    pairDouble :
      pairBase ≡ Fold.two * maskedBase
    pairDouble = foldPairedWeightedIsDoubleMasked system

    r744Orbit :
      R38.foldPower (R744.productionOrbitCell system) items
      ≡ R744.three * maskedBase
    r744Orbit = R744.foldProductionOrbit system
  in
  trans splitOrbit
    (trans
      (cong
        (λ value → value + value + value)
        pairDouble)
      (trans
        (solve (Fold.two ∷ R744.three ∷ maskedBase ∷ []))
        (cong
          (Fold.two *_)
          (sym r744Orbit))))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round748DyadicProductionPairedBeforeLocalEnergyCancellation : Bool
round748DyadicProductionPairedBeforeLocalEnergyCancellation = true

round748PairedDyadicProductionIsTwoDifferenceChannels : Bool
round748PairedDyadicProductionIsTwoDifferenceChannels = true

round748PairedProductionOrbitIsDoubleR744OrbitGlobally : Bool
round748PairedProductionOrbitIsDoubleR744OrbitGlobally = true

round748UsesActualDyadicCriticalWeight : Bool
round748UsesActualDyadicCriticalWeight = true

round748ImportsRadialR144Production : Bool
round748ImportsRadialR144Production = false

round748IntroducesEstimate : Bool
round748IntroducesEstimate = false

round748ClayPromotion : Bool
round748ClayPromotion = false

round748DyadicProductionPairedBeforeLocalEnergyCancellationIsTrue :
  round748DyadicProductionPairedBeforeLocalEnergyCancellation ≡ true
round748DyadicProductionPairedBeforeLocalEnergyCancellationIsTrue = refl

round748PairedDyadicProductionIsTwoDifferenceChannelsIsTrue :
  round748PairedDyadicProductionIsTwoDifferenceChannels ≡ true
round748PairedDyadicProductionIsTwoDifferenceChannelsIsTrue = refl

round748PairedProductionOrbitIsDoubleR744OrbitGloballyIsTrue :
  round748PairedProductionOrbitIsDoubleR744OrbitGlobally ≡ true
round748PairedProductionOrbitIsDoubleR744OrbitGloballyIsTrue = refl

round748UsesActualDyadicCriticalWeightIsTrue :
  round748UsesActualDyadicCriticalWeight ≡ true
round748UsesActualDyadicCriticalWeightIsTrue = refl

round748ImportsRadialR144ProductionIsFalse :
  round748ImportsRadialR144Production ≡ false
round748ImportsRadialR144ProductionIsFalse = refl

round748IntroducesEstimateIsFalse :
  round748IntroducesEstimate ≡ false
round748IntroducesEstimateIsFalse = refl

round748ClayPromotionIsFalse :
  round748ClayPromotion ≡ false
round748ClayPromotionIsFalse = refl
