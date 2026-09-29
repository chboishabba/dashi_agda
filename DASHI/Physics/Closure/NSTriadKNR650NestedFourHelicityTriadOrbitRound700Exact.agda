{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact where

------------------------------------------------------------------------
-- ROUND700 / EXPAND THE COMPLETE R696 ORBIT RESIDUE ONTO R694'S LITERAL
--            NESTED FOUR-HELICITY INNER TRIADS
--
-- R696 puts the selected global commutator on the complete cyclically closed
-- outer-triad carrier using a zero-output scalar mask:
--
--   R_triangle(beta)
--     = r*(beta) + r*(pLeg beta) + r*(qLeg beta).
--
-- R694 proves, cellwise on the SAME physical system,
--
--   NestedPair(alpha,beta) = 4 * CommutatorPair(alpha,beta),
--
-- where NestedPair contains the literal inner fibre a+b=p_beta and the four
-- R571 helicity multiplier-difference channels.
--
-- Therefore define the masked nested outer row and its three-leg orbit residue.
-- Exact finite summation gives
--
--   NestedR_triangle(beta) = 4 * R_triangle(beta)
--
-- pointwise, and hence globally
--
--   sum_beta NestedR_triangle(beta)
--     = 12 * C_N(inst).
--
-- No division, estimate, norm, absolute value, shell split, or new analytic
-- hypothesis is introduced.  This is the highest-alpha normal form for the
-- remaining nonlinear theorem: the analytic target is now literally the
-- signed complete outer-three-leg / inner-four-helicity incidence kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650MaskedCompleteTriadOrbitResidueRound696Exact as R696

F : C3.RealField _
F = Rational.rationalRealField

twelve : ℚ
twelve = 12

module NestedOrbit
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

  module Base = R696.MaskedOrbit physicalSystem S
  module Nested = R694.NestedExpansion
    physicalSystem S L H velocityTransverse

  nestedOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  nestedOuterRow beta =
    R546.spectatorRow
      Nested.nestedPair beta
      (Nested.Base.fibre (Physical.k beta))

  nestedRowIsFourCommutatorRow :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Nested.nestedPair beta items
    ≡
    R694.four *
      R546.spectatorRow Nested.Base.commutatorPair beta items
  nestedRowIsFourCommutatorRow beta [] =
    solve []
  nestedRowIsFourCommutatorRow beta (alpha ∷ rest) =
    trans
      (cong₂ _+_
        (Nested.nestedPairIsFourCommutatorPair alpha beta)
        (nestedRowIsFourCommutatorRow beta rest))
      (solve
        ( Nested.Base.commutatorPair alpha beta
        ∷ R546.spectatorRow Nested.Base.commutatorPair beta rest
        ∷ []))

  nestedOuterRowIsFourGlobalOuterRow :
    (beta : Physical.PhysicalTriadIncidence) →
    nestedOuterRow beta
    ≡ R694.four * Base.G.globalOuterRow beta
  nestedOuterRowIsFourGlobalOuterRow beta =
    nestedRowIsFourCommutatorRow
      beta (Nested.Base.fibre (Physical.k beta))

  maskedNestedOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  maskedNestedOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = nestedOuterRow beta

  maskedNestedOuterRowIsFourMaskedCommutatorRow :
    (beta : Physical.PhysicalTriadIncidence) →
    maskedNestedOuterRow beta
    ≡ R694.four * Base.maskedOuterRow beta
  maskedNestedOuterRowIsFourMaskedCommutatorRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = solve []
  ... | false = nestedOuterRowIsFourGlobalOuterRow beta

  nestedTriadOrbitResidue :
    Physical.PhysicalTriadIncidence → ℚ
  nestedTriadOrbitResidue beta =
    maskedNestedOuterRow beta
      + maskedNestedOuterRow (Orbit.pEnergyLeg beta)
      + maskedNestedOuterRow (Orbit.qEnergyLeg beta)

  nestedTriadOrbitResidueIsFourR696Residue :
    (beta : Physical.PhysicalTriadIncidence) →
    nestedTriadOrbitResidue beta
    ≡ R694.four * Base.triadOrbitResidue beta
  nestedTriadOrbitResidueIsFourR696Residue beta =
    trans
      (cong₂ _+_
        (cong₂ _+_
          (maskedNestedOuterRowIsFourMaskedCommutatorRow beta)
          (maskedNestedOuterRowIsFourMaskedCommutatorRow
            (Orbit.pEnergyLeg beta)))
        (maskedNestedOuterRowIsFourMaskedCommutatorRow
          (Orbit.qEnergyLeg beta)))
      (solve
        ( Base.maskedOuterRow beta
        ∷ Base.maskedOuterRow (Orbit.pEnergyLeg beta)
        ∷ Base.maskedOuterRow (Orbit.qEnergyLeg beta)
        ∷ []))

  foldNestedResidueIsFourR696 :
    (items : List Physical.PhysicalTriadIncidence) →
    R38.foldPower nestedTriadOrbitResidue items
    ≡ R694.four * R38.foldPower Base.triadOrbitResidue items
  foldNestedResidueIsFourR696 [] =
    solve []
  foldNestedResidueIsFourR696 (beta ∷ rest) =
    trans
      (cong₂ _+_
        (nestedTriadOrbitResidueIsFourR696Residue beta)
        (foldNestedResidueIsFourR696 rest))
      (solve
        ( Base.triadOrbitResidue beta
        ∷ R38.foldPower Base.triadOrbitResidue rest
        ∷ []))

  completeNestedTriadOrbitResidueIsTwelveCoherentCommutator :
    R38.foldPower nestedTriadOrbitResidue
      (Physical.physicalTriadEnumeration Nested.Base.cutoff)
    ≡
    twelve * Nested.Base.nonzeroGlobalCommutatorWork
  completeNestedTriadOrbitResidueIsTwelveCoherentCommutator =
    let
      items = Physical.physicalTriadEnumeration Nested.Base.cutoff
      comm = Nested.Base.nonzeroGlobalCommutatorWork
    in
    trans
      (foldNestedResidueIsFourR696 items)
      (trans
        (cong
          (R694.four *_)
          Base.completeTriadOrbitResidueIsThreeCoherentCommutator)
        (solve (comm ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round700R696OrbitResidueExpandedOntoLiteralNestedFourHelicityCarrier : Bool
round700R696OrbitResidueExpandedOntoLiteralNestedFourHelicityCarrier = true

round700NestedOrbitResidueIsFourR696ResiduePointwise : Bool
round700NestedOrbitResidueIsFourR696ResiduePointwise = true

round700CompleteNestedOrbitResidueIsTwelveCoherentCommutator : Bool
round700CompleteNestedOrbitResidueIsTwelveCoherentCommutator = true

round700InnerCarrierUsesLiteralPhysicalOutputFibre : Bool
round700InnerCarrierUsesLiteralPhysicalOutputFibre = true

round700OuterCarrierUsesCompletePhysicalTriadEnumeration : Bool
round700OuterCarrierUsesCompletePhysicalTriadEnumeration = true

round700IntroducesEstimate : Bool
round700IntroducesEstimate = false

round700IntroducesNormOrAbsoluteValue : Bool
round700IntroducesNormOrAbsoluteValue = false

round700NestedOrbitSignedPaymentClosed : Bool
round700NestedOrbitSignedPaymentClosed = false

round700ClayPromotion : Bool
round700ClayPromotion = false

round700R696OrbitResidueExpandedOntoLiteralNestedFourHelicityCarrierIsTrue :
  round700R696OrbitResidueExpandedOntoLiteralNestedFourHelicityCarrier ≡ true
round700R696OrbitResidueExpandedOntoLiteralNestedFourHelicityCarrierIsTrue = refl

round700NestedOrbitResidueIsFourR696ResiduePointwiseIsTrue :
  round700NestedOrbitResidueIsFourR696ResiduePointwise ≡ true
round700NestedOrbitResidueIsFourR696ResiduePointwiseIsTrue = refl

round700CompleteNestedOrbitResidueIsTwelveCoherentCommutatorIsTrue :
  round700CompleteNestedOrbitResidueIsTwelveCoherentCommutator ≡ true
round700CompleteNestedOrbitResidueIsTwelveCoherentCommutatorIsTrue = refl

round700IntroducesEstimateIsFalse :
  round700IntroducesEstimate ≡ false
round700IntroducesEstimateIsFalse = refl

round700IntroducesNormOrAbsoluteValueIsFalse :
  round700IntroducesNormOrAbsoluteValue ≡ false
round700IntroducesNormOrAbsoluteValueIsFalse = refl

round700NestedOrbitSignedPaymentClosedIsFalse :
  round700NestedOrbitSignedPaymentClosed ≡ false
round700NestedOrbitSignedPaymentClosedIsFalse = refl

round700ClayPromotionIsFalse :
  round700ClayPromotion ≡ false
round700ClayPromotionIsFalse = refl
