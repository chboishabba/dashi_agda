{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SwapPairedNestedOrbitNormalFormRound763Exact where

------------------------------------------------------------------------
-- ROUND763 / LIFT THE R762 SWAP-PAIRED PRODUCT-RULE IDENTITY THROUGH THE
--            SPECTATOR ROW, ZERO-OUTPUT MASK, AND THREE-LEG NESTED ORBIT
--
-- R762:
--
--   NestedCell(beta)+NestedCell(swap beta)
--     = FourCopies(Product(beta)+Product(swap beta)).
--
-- Since beta and swap beta have the same output k, the spectator fibre is
-- literally the same.  Coherent-work additivity therefore gives one paired
-- base row on the paired product-rule forcing.
--
-- For the complete three-leg orbit, R119 exchanges the p/q energy legs:
--
--   pLeg(swap beta)=qLeg(beta),
--   qLeg(swap beta)=pLeg(beta).
--
-- Hence exactly
--
--   NestedOrbit(beta)+NestedOrbit(swap beta)
--     = PairedBaseProductRuleRow(beta)
--       + 2 MaskedNestedRow(pLeg beta)
--       + 2 MaskedNestedRow(qLeg beta).
--
-- No estimate, sign, norm, or division is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeFullSwapAntisymmetryRound119Exact as R119
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700
import DASHI.Physics.Closure.NSTriadKNR650NestedSwapPairProductRuleRound762Exact as R762

F : C3.RealField _
F = Rational.rationalRealField

two : ℚ
two = 2

module PairedNestedOrbit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module N =
    R700.NestedOrbit
      physicalSystem S L H velocityTransverse

  module Pair =
    R762.NestedSwapPair
      physicalSystem S L H velocityTransverse

  pairedProductRuleNestedPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  pairedProductRuleNestedPair alpha beta =
    Work.coherentWork
      (N.Nested.Base.mixedCell alpha)
      (R762.fourCopies (Pair.pairedProductRuleCell beta))

  nestedPairSwapSumIsPairedProductRule :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    N.Nested.nestedPair alpha beta
      + N.Nested.nestedPair alpha (Symmetry.swapTriad beta)
    ≡ pairedProductRuleNestedPair alpha beta
  nestedPairSwapSumIsPairedProductRule alpha beta =
    let
      mixed = N.Nested.Base.mixedCell alpha
      left = N.Nested.nestedCell beta
      right = N.Nested.nestedCell (Symmetry.swapTriad beta)
    in
    trans
      (sym (Work.workAddRight mixed left right))
      (cong
        (Work.coherentWork mixed)
        (Pair.nestedSwapPairIsFourProductRuleCopies beta))

  pairedProductRuleOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  pairedProductRuleOuterRow beta =
    R546.spectatorRow
      pairedProductRuleNestedPair beta
      (N.Nested.Base.fibre (Physical.k beta))

  spectatorRowsSwapPair :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow N.Nested.nestedPair beta items
      + R546.spectatorRow
          N.Nested.nestedPair (Symmetry.swapTriad beta) items
    ≡
    R546.spectatorRow pairedProductRuleNestedPair beta items
  spectatorRowsSwapPair beta [] = solve []
  spectatorRowsSwapPair beta (alpha ∷ rest) =
    trans
      (cong₂ _+_
        (cong₂ _+_
          refl
          (spectatorRowsSwapPair beta rest))
        refl)
      (trans
        (solve
          ( N.Nested.nestedPair alpha beta
          ∷ N.Nested.nestedPair alpha (Symmetry.swapTriad beta)
          ∷ R546.spectatorRow N.Nested.nestedPair beta rest
          ∷ R546.spectatorRow
              N.Nested.nestedPair (Symmetry.swapTriad beta) rest
          ∷ []))
        (cong
          (_+ R546.spectatorRow pairedProductRuleNestedPair beta rest)
          (nestedPairSwapSumIsPairedProductRule alpha beta)))

  nestedOuterRowSwapPair :
    (beta : Physical.PhysicalTriadIncidence) →
    N.nestedOuterRow beta
      + N.nestedOuterRow (Symmetry.swapTriad beta)
    ≡ pairedProductRuleOuterRow beta
  nestedOuterRowSwapPair beta
    rewrite Symmetry.swapTriadK beta =
    spectatorRowsSwapPair beta
      (N.Nested.Base.fibre (Physical.k beta))

  pairedMaskedBaseRow :
    Physical.PhysicalTriadIncidence → ℚ
  pairedMaskedBaseRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = pairedProductRuleOuterRow beta

  maskedNestedOuterRowSwapPair :
    (beta : Physical.PhysicalTriadIncidence) →
    N.maskedNestedOuterRow beta
      + N.maskedNestedOuterRow (Symmetry.swapTriad beta)
    ≡ pairedMaskedBaseRow beta
  maskedNestedOuterRowSwapPair beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true
    rewrite Symmetry.swapTriadK beta = solve []
  ... | false
    rewrite Symmetry.swapTriadK beta =
      nestedOuterRowSwapPair beta

  nestedOrbitSwapPairNormalForm :
    (beta : Physical.PhysicalTriadIncidence) →
    N.nestedTriadOrbitResidue beta
      + N.nestedTriadOrbitResidue (Symmetry.swapTriad beta)
    ≡
    pairedMaskedBaseRow beta
      + two * N.maskedNestedOuterRow (Orbit.pEnergyLeg beta)
      + two * N.maskedNestedOuterRow (Orbit.qEnergyLeg beta)
  nestedOrbitSwapPairNormalForm beta =
    let
      base = N.maskedNestedOuterRow beta
      baseSwap = N.maskedNestedOuterRow (Symmetry.swapTriad beta)
      p = N.maskedNestedOuterRow (Orbit.pEnergyLeg beta)
      q = N.maskedNestedOuterRow (Orbit.qEnergyLeg beta)

      expose :
        N.nestedTriadOrbitResidue beta
          + N.nestedTriadOrbitResidue (Symmetry.swapTriad beta)
        ≡
        (base + p + q)
          + (baseSwap + q + p)
      expose =
        cong₂ _+_
          refl
          (cong₂ _+_
            (cong₂ _+_
              refl
              (cong N.maskedNestedOuterRow
                (R119.pEnergyLegSwapIsQEnergyLeg beta)))
            (cong N.maskedNestedOuterRow
              (R119.qEnergyLegSwapIsPEnergyLeg beta)))
    in
    trans expose
      (trans
        (solve
          ( base
          ∷ baseSwap
          ∷ p
          ∷ q
          ∷ pairedMaskedBaseRow beta
          ∷ two
          ∷ []))
        (cong
          (λ paired →
            paired + two * p + two * q)
          (maskedNestedOuterRowSwapPair beta)))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round763BaseNestedSwapPairIsProductRuleRow : Bool
round763BaseNestedSwapPairIsProductRuleRow = true

round763MaskedBaseSwapPairClosed : Bool
round763MaskedBaseSwapPairClosed = true

round763NestedOrbitSwapPairNormalFormClosed : Bool
round763NestedOrbitSwapPairNormalFormClosed = true

round763RemainingCyclicRowsAreDoubledPAndQ : Bool
round763RemainingCyclicRowsAreDoubledPAndQ = true

round763IntroducesEstimate : Bool
round763IntroducesEstimate = false

round763IntroducesNormOrAbsoluteValue : Bool
round763IntroducesNormOrAbsoluteValue = false

round763ClayPromotion : Bool
round763ClayPromotion = false

round763BaseNestedSwapPairIsProductRuleRowIsTrue :
  round763BaseNestedSwapPairIsProductRuleRow ≡ true
round763BaseNestedSwapPairIsProductRuleRowIsTrue = refl

round763MaskedBaseSwapPairClosedIsTrue :
  round763MaskedBaseSwapPairClosed ≡ true
round763MaskedBaseSwapPairClosedIsTrue = refl

round763NestedOrbitSwapPairNormalFormClosedIsTrue :
  round763NestedOrbitSwapPairNormalFormClosed ≡ true
round763NestedOrbitSwapPairNormalFormClosedIsTrue = refl

round763RemainingCyclicRowsAreDoubledPAndQIsTrue :
  round763RemainingCyclicRowsAreDoubledPAndQ ≡ true
round763RemainingCyclicRowsAreDoubledPAndQIsTrue = refl

round763IntroducesEstimateIsFalse :
  round763IntroducesEstimate ≡ false
round763IntroducesEstimateIsFalse = refl

round763IntroducesNormOrAbsoluteValueIsFalse :
  round763IntroducesNormOrAbsoluteValue ≡ false
round763IntroducesNormOrAbsoluteValueIsFalse = refl

round763ClayPromotionIsFalse :
  round763ClayPromotion ≡ false
round763ClayPromotionIsFalse = refl
