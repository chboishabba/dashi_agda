{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650CriticalProductionIncidenceCarrierRound744Exact where

------------------------------------------------------------------------
-- ROUND744 / CRITICAL PRODUCTION ON THE COMPLETE PHYSICAL TRIAD CARRIER
--
-- S2a writes literal critical production as twice the dyadic-weighted R39
-- output pairing.  R39 partitions the complete physical incidence enumeration
-- into exact output fibres.  This owner pushes the dyadic output weight through
-- that partition and obtains one cell on the SAME carrier used by R700/R723:
--
--   productionCell(tau)
--     = lambda(k_tau) * orderedPower(tau).
--
-- On the canonical cutoff support:
--
--   criticalProduction = 2 * sum_tau productionCell(tau).
--
-- The R38 p/q energy-leg permutations then give the exact cyclic orbit
--
--   productionOrbit(tau)
--     = productionCell(tau)
--       + productionCell(pLeg tau)
--       + productionCell(qLeg tau),
--
-- with
--
--   sum productionOrbit = 3 * sum productionCell.
--
-- No estimate, sign choice, shell decomposition, or division is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNF4GlobalOutputFiberPartitionRound39Exact as Global39
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold
import DASHI.Physics.Closure.NSTriadKNLiteralCriticalProductionProjectedPairingExact as S2a

F : C3.RealField _
F = Rational.rationalRealField

three : ℚ
three = 3

productionCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence →
  ℚ
productionCell {E} {I} system tau =
  Fold.dyadicCriticalWeight (Physical.k tau)
    * R38.orderedPower E I tau (Audit.velocity system)

weightedOutputPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Z3.FourierMode → ℚ
weightedOutputPairing system output =
  Fold.dyadicCriticalWeight output
    * R39.realHermitianPower
        (Audit.velocity system output)
        (Audit.projectedNonlinearity system output)

sumWeightedOutputs :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  List Z3.FourierMode → ℚ
sumWeightedOutputs system [] = 0ℚ
sumWeightedOutputs system (output ∷ rest) =
  weightedOutputPairing system output
    + sumWeightedOutputs system rest

weightedOutputIsProductionCellFibre :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (output : Z3.FourierMode) →
  weightedOutputPairing system output
  ≡
  R38.foldPower (productionCell system)
    (Output.physicalOutputFiber (Audit.cutoff system) output)
weightedOutputIsProductionCellFibre {E} {I} system output =
  let
    fibre = Output.physicalOutputFiber (Audit.cutoff system) output
    raw =
      R39.projectedOutputEnergyPairingEqualsOrderedFiberFold system output

    scaleFold :
      Fold.dyadicCriticalWeight output
        * R38.foldPower
            (λ tau → R38.orderedPower E I tau (Audit.velocity system))
            fibre
      ≡ R38.foldPower (productionCell system) fibre
    scaleFold = go fibre
      (λ tau member → Output.physicalOutputFiberSound member)
      where
      go :
        (items : List Physical.PhysicalTriadIncidence) →
        ((tau : Physical.PhysicalTriadIncidence) →
          tau Cube.∈ items → Physical.k tau ≡ output) →
        Fold.dyadicCriticalWeight output
          * R38.foldPower
              (λ tau → R38.orderedPower E I tau (Audit.velocity system))
              items
        ≡ R38.foldPower (productionCell system) items
      go [] allOutput = solve []
      go (tau ∷ rest) allOutput =
        let
          kEq = allOutput tau (Cube.here refl)
          tail = λ selected member → allOutput selected (Cube.there member)
        in
        trans
          (solve
            ( Fold.dyadicCriticalWeight output
            ∷ R38.orderedPower E I tau (Audit.velocity system)
            ∷ R38.foldPower
                (λ selected →
                  R38.orderedPower E I selected (Audit.velocity system))
                rest
            ∷ []))
          (cong₂ _+_
            (subst
              (λ mode →
                Fold.dyadicCriticalWeight output
                  * R38.orderedPower E I tau (Audit.velocity system)
                ≡
                Fold.dyadicCriticalWeight mode
                  * R38.orderedPower E I tau (Audit.velocity system))
              (sym kEq) refl)
            (go rest tail))
  in
  trans
    (cong (Fold.dyadicCriticalWeight output *_) raw)
    scaleFold

sumWeightedOutputsIsConcatProductionFold :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (outputs : List Z3.FourierMode) →
  sumWeightedOutputs system outputs
  ≡
  R38.foldPower (productionCell system)
    (Global39.concatOutputFibers (Audit.cutoff system) outputs)
sumWeightedOutputsIsConcatProductionFold system [] = refl
sumWeightedOutputsIsConcatProductionFold system (output ∷ rest) =
  trans
    (cong₂ _+_
      (weightedOutputIsProductionCellFibre system output)
      (sumWeightedOutputsIsConcatProductionFold system rest))
    (sym
      (Global39.foldAppend
        (productionCell system)
        (Output.physicalOutputFiber (Audit.cutoff system) output)
        (Global39.concatOutputFibers (Audit.cutoff system) rest)))

canonicalWeightedOutputSumIsFullProductionFold :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  sumWeightedOutputs system (Cube.cutoffModes (Audit.cutoff system))
  ≡
  R38.foldPower (productionCell system)
    (Physical.physicalTriadEnumeration (Audit.cutoff system))
canonicalWeightedOutputSumIsFullProductionFold system =
  trans
    (sumWeightedOutputsIsConcatProductionFold
      system (Cube.cutoffModes (Audit.cutoff system)))
    (R38.foldPermutationInvariant
      (productionCell system)
      (Global39.literalOutputPartitionPermutation (Audit.cutoff system)))

sumWeightedOutputsIsS2aWeightedPairing :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  (outputs : List Z3.FourierMode) →
  sumWeightedOutputs system outputs
  ≡ S2a.weightedProjectedPairing system outputs
sumWeightedOutputsIsS2aWeightedPairing system [] = refl
sumWeightedOutputsIsS2aWeightedPairing system (output ∷ rest) =
  cong₂ _+_ refl
    (sumWeightedOutputsIsS2aWeightedPairing system rest)

criticalProductionIsTwiceFullIncidenceFold :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  Audit.modes system ≡ Cube.cutoffModes (Audit.cutoff system) →
  Fold.criticalProductionRate system
  ≡
  Fold.two *
    R38.foldPower (productionCell system)
      (Physical.physicalTriadEnumeration (Audit.cutoff system))
criticalProductionIsTwiceFullIncidenceFold system modesExact =
  trans
    (S2a.literalCriticalProductionIsTwiceWeightedProjectedPairing system)
    (trans
      (cong
        (Fold.two *_)
        (subst
          (λ modes →
            S2a.weightedProjectedPairing system (Audit.modes system)
            ≡ S2a.weightedProjectedPairing system modes)
          modesExact refl))
      (trans
        (cong
          (Fold.two *_)
          (sym
            (sumWeightedOutputsIsS2aWeightedPairing
              system (Cube.cutoffModes (Audit.cutoff system)))))
        (cong
          (Fold.two *_)
          (canonicalWeightedOutputSumIsFullProductionFold system))))

productionOrbitCell :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  Audit.FiniteComplex3GalerkinSystem F E I →
  Physical.PhysicalTriadIncidence → ℚ
productionOrbitCell system tau =
  productionCell system tau
    + productionCell system (Orbit.pEnergyLeg tau)
    + productionCell system (Orbit.qEnergyLeg tau)

foldProductionOrbit :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E} →
  (system : Audit.FiniteComplex3GalerkinSystem F E I) →
  R38.foldPower (productionOrbitCell system)
    (Physical.physicalTriadEnumeration (Audit.cutoff system))
  ≡
  three *
    R38.foldPower (productionCell system)
      (Physical.physicalTriadEnumeration (Audit.cutoff system))
foldProductionOrbit system =
  let
    items = Physical.physicalTriadEnumeration (Audit.cutoff system)
    base = R38.foldPower (productionCell system) items

    pInvariant :
      R38.foldPower
        (λ tau → productionCell system (Orbit.pEnergyLeg tau)) items
      ≡ base
    pInvariant =
      trans
        (sym
          (R38.foldMap
            (productionCell system) Orbit.pEnergyLeg items))
        (R38.foldPermutationInvariant
          (productionCell system)
          (R38.pEnergyLegEnumerationPermutation (Audit.cutoff system)))

    qInvariant :
      R38.foldPower
        (λ tau → productionCell system (Orbit.qEnergyLeg tau)) items
      ≡ base
    qInvariant =
      trans
        (sym
          (R38.foldMap
            (productionCell system) Orbit.qEnergyLeg items))
        (R38.foldPermutationInvariant
          (productionCell system)
          (R38.qEnergyLegEnumerationPermutation (Audit.cutoff system)))

    split = go items
      where
      go :
        (xs : List Physical.PhysicalTriadIncidence) →
        R38.foldPower (productionOrbitCell system) xs
        ≡
        R38.foldPower (productionCell system) xs
          + R38.foldPower
              (λ tau → productionCell system (Orbit.pEnergyLeg tau)) xs
          + R38.foldPower
              (λ tau → productionCell system (Orbit.qEnergyLeg tau)) xs
      go [] = solve []
      go (tau ∷ rest) =
        trans
          (cong (productionOrbitCell system tau +_) (go rest))
          (solve
            ( productionCell system tau
            ∷ productionCell system (Orbit.pEnergyLeg tau)
            ∷ productionCell system (Orbit.qEnergyLeg tau)
            ∷ R38.foldPower (productionCell system) rest
            ∷ R38.foldPower
                (λ selected →
                  productionCell system (Orbit.pEnergyLeg selected)) rest
            ∷ R38.foldPower
                (λ selected →
                  productionCell system (Orbit.qEnergyLeg selected)) rest
            ∷ []))
  in
  trans split
    (trans
      (cong₂ _+_ refl (cong₂ _+_ pInvariant qInvariant))
      (solve (base ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round744CriticalProductionOnCompletePhysicalIncidenceCarrier : Bool
round744CriticalProductionOnCompletePhysicalIncidenceCarrier = true

round744ProductionOrbitUsesSameR38ThreeLegCarrierAsR700 : Bool
round744ProductionOrbitUsesSameR38ThreeLegCarrierAsR700 = true

round744ProductionOrbitFoldIsThreeCopies : Bool
round744ProductionOrbitFoldIsThreeCopies = true

round744IntroducesEstimate : Bool
round744IntroducesEstimate = false

round744ClayPromotion : Bool
round744ClayPromotion = false

round744CriticalProductionOnCompletePhysicalIncidenceCarrierIsTrue :
  round744CriticalProductionOnCompletePhysicalIncidenceCarrier ≡ true
round744CriticalProductionOnCompletePhysicalIncidenceCarrierIsTrue = refl

round744ProductionOrbitUsesSameR38ThreeLegCarrierAsR700IsTrue :
  round744ProductionOrbitUsesSameR38ThreeLegCarrierAsR700 ≡ true
round744ProductionOrbitUsesSameR38ThreeLegCarrierAsR700IsTrue = refl

round744ProductionOrbitFoldIsThreeCopiesIsTrue :
  round744ProductionOrbitFoldIsThreeCopies ≡ true
round744ProductionOrbitFoldIsThreeCopiesIsTrue = refl

round744IntroducesEstimateIsFalse :
  round744IntroducesEstimate ≡ false
round744IntroducesEstimateIsFalse = refl

round744ClayPromotionIsFalse :
  round744ClayPromotion ≡ false
round744ClayPromotionIsFalse = refl
