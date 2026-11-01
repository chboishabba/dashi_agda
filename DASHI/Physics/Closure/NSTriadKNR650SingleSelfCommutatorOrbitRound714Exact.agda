{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SingleSelfCommutatorOrbitRound714Exact where

------------------------------------------------------------------------
-- ROUND714 / REMOVE THE LITERAL FOUR-COPY DUPLICATION FROM THE COMPLETE
--            R713 SELF ORBIT
--
-- R713 puts the complete R708 self orbit on R712's exhaustive carrier
--
--   Self4*(tau) = 0                      if p_tau = 0,
--               = C_tau+C_tau+C_tau+C_tau otherwise,
--
-- where C_tau is the selected-self mixed commutator.
--
-- Coherent work is additive in its right slot.  Therefore the factor four can
-- be pulled through the complete spectator row, the k=0 mask, the three outer
-- energy legs, and the complete physical-triad enumeration:
--
--   CompleteSelfOrbit = 4 * CompleteSingleSelfCommutatorOrbit.
--
-- This leaves the exact-cancellation test on ONE copy of the commutator scalar
-- orbit.  No estimate, norm, positivity, or cancellation is asserted.
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
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNA3CenteredKernelNormalFormExact as A3
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SelfOrbitCommutatorCarrierRound713Exact as R713

module SingleSelfOrbit
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Carrier =
    R713.SelfOrbitCarrier physicalSystem S L H velocityTransverse

  singleSelfCommutator :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  singleSelfCommutator tau
    with Output.modeEqual (Physical.p tau) Z3.zeroMode
  ... | true = C3.complex3Zero R694.F
  ... | false = Carrier.Normal.SelfSlot.Self.selfCommutatorCell tau

  singlePair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  singlePair alpha beta =
    Work.coherentWork
      (Carrier.Split.Full.Nested.Base.mixedCell alpha)
      (singleSelfCommutator beta)

  commutatorPairIsFourSinglePair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Carrier.commutatorPair alpha beta
    ≡ A3.four * singlePair alpha beta
  commutatorPairIsFourSinglePair alpha beta
    with Output.modeEqual (Physical.p beta) Z3.zeroMode
  ... | true =
    trans
      (R597.workZeroRight
        (Carrier.Split.Full.Nested.Base.mixedCell alpha))
      (solve [])
  ... | false =
    A3.workFourCopies
      (Carrier.Split.Full.Nested.Base.mixedCell alpha)
      (Carrier.Normal.SelfSlot.Self.selfCommutatorCell beta)

  singleOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  singleOuterRow beta =
    R546.spectatorRow singlePair beta
      (Carrier.Split.Full.Nested.Base.fibre (Physical.k beta))

  rowIsFourSingle :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Carrier.commutatorPair beta items
    ≡ A3.four * R546.spectatorRow singlePair beta items
  rowIsFourSingle beta [] = solve []
  rowIsFourSingle beta (alpha ∷ rest) =
    trans
      (cong₂ _+_
        (commutatorPairIsFourSinglePair alpha beta)
        (rowIsFourSingle beta rest))
      (solve
        ( singlePair alpha beta
        ∷ R546.spectatorRow singlePair beta rest
        ∷ []))

  commutatorOuterRowIsFourSingle :
    (beta : Physical.PhysicalTriadIncidence) →
    Carrier.commutatorOuterRow beta
    ≡ A3.four * singleOuterRow beta
  commutatorOuterRowIsFourSingle beta =
    rowIsFourSingle beta
      (Carrier.Split.Full.Nested.Base.fibre (Physical.k beta))

  maskedSingleOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  maskedSingleOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = singleOuterRow beta

  maskedCommutatorOuterRowIsFourSingle :
    (beta : Physical.PhysicalTriadIncidence) →
    Carrier.maskedCommutatorOuterRow beta
    ≡ A3.four * maskedSingleOuterRow beta
  maskedCommutatorOuterRowIsFourSingle beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = solve []
  ... | false = commutatorOuterRowIsFourSingle beta

  singleOrbitResidue :
    Physical.PhysicalTriadIncidence → ℚ
  singleOrbitResidue beta =
    maskedSingleOuterRow beta
      + maskedSingleOuterRow (Orbit.pEnergyLeg beta)
      + maskedSingleOuterRow (Orbit.qEnergyLeg beta)

  commutatorOrbitResidueIsFourSingle :
    (beta : Physical.PhysicalTriadIncidence) →
    Carrier.commutatorOrbitResidue beta
    ≡ A3.four * singleOrbitResidue beta
  commutatorOrbitResidueIsFourSingle beta =
    trans
      (cong₂ _+_
        (cong₂ _+_
          (maskedCommutatorOuterRowIsFourSingle beta)
          (maskedCommutatorOuterRowIsFourSingle
            (Orbit.pEnergyLeg beta)))
        (maskedCommutatorOuterRowIsFourSingle
          (Orbit.qEnergyLeg beta)))
      (solve
        ( maskedSingleOuterRow beta
        ∷ maskedSingleOuterRow (Orbit.pEnergyLeg beta)
        ∷ maskedSingleOuterRow (Orbit.qEnergyLeg beta)
        ∷ []))

  foldSingleOrbit :
    List Physical.PhysicalTriadIncidence → ℚ
  foldSingleOrbit = R38.foldPower singleOrbitResidue

  foldCommutatorOrbitIsFourSingle :
    (items : List Physical.PhysicalTriadIncidence) →
    Carrier.foldCommutatorOrbit items
    ≡ A3.four * foldSingleOrbit items
  foldCommutatorOrbitIsFourSingle [] = solve []
  foldCommutatorOrbitIsFourSingle (beta ∷ rest) =
    trans
      (cong₂ _+_
        (commutatorOrbitResidueIsFourSingle beta)
        (foldCommutatorOrbitIsFourSingle rest))
      (solve
        ( singleOrbitResidue beta
        ∷ foldSingleOrbit rest
        ∷ []))

  completeSelfOrbitIsFourSingleSelfCommutatorOrbit :
    Carrier.Split.foldSelfOrbit
      (Physical.physicalTriadEnumeration
        Carrier.Split.Full.Nested.Base.cutoff)
    ≡
    A3.four *
      foldSingleOrbit
        (Physical.physicalTriadEnumeration
          Carrier.Split.Full.Nested.Base.cutoff)
  completeSelfOrbitIsFourSingleSelfCommutatorOrbit =
    trans
      Carrier.completeSelfOrbitIsCompleteCommutatorOrbit
      (foldCommutatorOrbitIsFourSingle
        (Physical.physicalTriadEnumeration
          Carrier.Split.Full.Nested.Base.cutoff))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round714CompleteSelfOrbitIsFourSingleSelfCommutatorOrbit : Bool
round714CompleteSelfOrbitIsFourSingleSelfCommutatorOrbit = true

round714SingleCarrierPreservesPZeroAndKZeroBranches : Bool
round714SingleCarrierPreservesPZeroAndKZeroBranches = true

round714SelfOrbitExactCancellationClosed : Bool
round714SelfOrbitExactCancellationClosed = false

round714IntroducesEstimate : Bool
round714IntroducesEstimate = false

round714ClayPromotion : Bool
round714ClayPromotion = false

round714CompleteSelfOrbitIsFourSingleSelfCommutatorOrbitIsTrue :
  round714CompleteSelfOrbitIsFourSingleSelfCommutatorOrbit ≡ true
round714CompleteSelfOrbitIsFourSingleSelfCommutatorOrbitIsTrue = refl

round714SingleCarrierPreservesPZeroAndKZeroBranchesIsTrue :
  round714SingleCarrierPreservesPZeroAndKZeroBranches ≡ true
round714SingleCarrierPreservesPZeroAndKZeroBranchesIsTrue = refl

round714SelfOrbitExactCancellationClosedIsFalse :
  round714SelfOrbitExactCancellationClosed ≡ false
round714SelfOrbitExactCancellationClosedIsFalse = refl

round714IntroducesEstimateIsFalse :
  round714IntroducesEstimate ≡ false
round714IntroducesEstimateIsFalse = refl

round714ClayPromotionIsFalse :
  round714ClayPromotion ≡ false
round714ClayPromotionIsFalse = refl
