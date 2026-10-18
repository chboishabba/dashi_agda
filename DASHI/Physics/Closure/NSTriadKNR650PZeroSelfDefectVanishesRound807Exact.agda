{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650PZeroSelfDefectVanishesRound807Exact where

------------------------------------------------------------------------
-- ROUND807 / THE R804 p=0 SELECTED-SELF DEFECT VANISHES EXACTLY
--
-- R804 conservatively isolated a p=0 provenance branch because a generic
-- finite-system velocity lookup is not itself identified with the canonical
-- mean-zero lookup.
--
-- That stronger lookup statement is unnecessary.
--
-- For beta=(p,q->k), R95 defines selfForcingP(beta) by applying the selected
-- ordered-pair forcing to pEnergyLeg(beta), whose output is exactly old p.
-- Therefore when p=0 both selected ordered Galerkin interactions have output
-- zero.  R436 proves EACH projected ordered interaction at output zero vanishes
-- from resonance + all-mode transversality alone.
--
-- Hence:
--
--   p_beta = 0
--     -> selfForcingP(beta) = 0
--     -> R710.selfCommutatorCell(beta) = 0
--     -> R804.pZeroSelfDefect(beta) = 0.
--
-- Folding and coherent work then give globally
--
--   C_{p=0,sep} = 0.
--
-- No mean-zero lookup assumption, estimate, norm, or absolute value is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfZeroSafeSplitRound804Exact as R804

module PZeroDefectVanishes
    (physicalSystem :
      Field30.PhysicalFiniteComplex3GalerkinSystem R804.R803.R802.F)
    (S : Helical.HelicalModeScalars R804.R803.R802.F)
    (L : Helical.PeriodicHelicalProjectorLaws R804.R803.R802.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module Sep =
    R804.SeparatedSelfZeroSafe
      physicalSystem S L H velocityTransverse

  system = Field30.finiteSystem physicalSystem
  velocity = Audit.velocity system
  cutoff = Sep.cutoff

  selfForcingPAtPZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.p beta ≡ Z3.zeroMode →
    R95.selfForcingP system beta
    ≡ C3.complex3Zero R804.R803.R802.F
  selfForcingPAtPZero beta pZero =
    let
      leg = Orbit.pEnergyLeg beta

      legOutputZero :
        Physical.k leg ≡ Z3.zeroMode
      legOutputZero =
        trans (Orbit.pEnergyLegOutput beta) pZero

      swapOutputZero :
        Physical.k (Symmetry.swapTriad leg) ≡ Z3.zeroMode
      swapOutputZero =
        trans
          (Symmetry.swapTriadK leg)
          legOutputZero

      firstZero :
        Audit.projectedOrderedTerm system leg
        ≡ C3.complex3Zero R804.R803.R802.F
      firstZero =
        R436.projectedOrderedTermAtZeroOutputIsZero
          system velocityTransverse leg legOutputZero

      secondZero :
        Audit.projectedOrderedTerm system (Symmetry.swapTriad leg)
        ≡ C3.complex3Zero R804.R803.R802.F
      secondZero =
        R436.projectedOrderedTermAtZeroOutputIsZero
          system velocityTransverse
          (Symmetry.swapTriad leg)
          swapOutputZero
    in
    trans
      (R111.selfForcingKIsTwoSelectedOrderedTerms system leg)
      (trans
        (cong₂ C3.complex3Add firstZero secondZero)
        (R230.complex3AddZeroLeft
          (C3.complex3Zero R804.R803.R802.F)))

  selfCommutatorAtPZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.p beta ≡ Z3.zeroMode →
    Sep.Sep.Self.selfCommutatorCell beta
    ≡ C3.complex3Zero R804.R803.R802.F
  selfCommutatorAtPZero beta pZero =
    let
      selfP = R95.selfForcingP system beta

      forcing :
        Z3.FourierMode → C3.Complex3 R804.R803.R802.F
      forcing mode = selfP

      forcingZero :
        forcing (Physical.p beta)
        ≡ C3.complex3Zero R804.R803.R802.F
      forcingZero = selfForcingPAtPZero beta pZero
    in
    R437.forcingCommutatorZeroFromForcingZero
      S velocity forcing beta forcingZero

  pZeroDefectCellIsZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Sep.pZeroSelfDefect beta
    ≡ C3.complex3Zero R804.R803.R802.F
  pZeroDefectCellIsZero beta
    with R781.ccTouched beta
       | Output.modeEqual (Physical.p beta) Z3.zeroMode in pDecision
  ... | true | decision = refl
  ... | false | true =
    selfCommutatorAtPZero beta
      (Output.modeEqualSound pDecision)
  ... | false | false = refl

  pZeroDefectFoldIsZero :
    (output : Z3.FourierMode) →
    Sep.pZeroDefectFold output
    ≡ C3.complex3Zero R804.R803.R802.F
  pZeroDefectFoldIsZero output =
    go (Output.physicalOutputFiber cutoff output)
    where
    go :
      (items : List Physical.PhysicalTriadIncidence) →
      R224.foldVector Sep.pZeroSelfDefect items
      ≡ C3.complex3Zero R804.R803.R802.F
    go [] = refl
    go (beta ∷ rest) =
      trans
        (cong₂ C3.complex3Add
          (pZeroDefectCellIsZero beta)
          (go rest))
        (R230.complex3AddZeroLeft
          (C3.complex3Zero R804.R803.R802.F))

  selectedPZeroDefectWorkIsZero :
    (output : Z3.FourierMode) →
    Sep.selectedPZeroDefectWork output ≡ 0ℚ
  selectedPZeroDefectWorkIsZero output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false =
    trans
      (cong
        (Work.coherentWork (Sep.Sep.Split.Id.mixedFold output))
        (pZeroDefectFoldIsZero output))
      (R597.workZeroRight
        (Sep.Sep.Split.Id.mixedFold output))

  globalPZeroSelfDefectWorkIsZero :
    Sep.globalPZeroSelfDefectWork ≡ 0ℚ
  globalPZeroSelfDefectWorkIsZero =
    go (Cube.cutoffModes cutoff)
    where
    go :
      (outputs : List Z3.FourierMode) →
      Sep.sumPZeroDefectWork outputs ≡ 0ℚ
    go [] = refl
    go (output ∷ rest) =
      trans
        (cong₂ _+_
          (selectedPZeroDefectWorkIsZero output)
          (go rest))
        refl

round807PZeroSelectedSelfForcingVanishes : Bool
round807PZeroSelectedSelfForcingVanishes = true

round807PZeroSelfCommutatorVanishes : Bool
round807PZeroSelfCommutatorVanishes = true

round807GlobalPZeroDefectVanishes : Bool
round807GlobalPZeroDefectVanishes = true

round807UsesMeanZeroLookupAssumption : Bool
round807UsesMeanZeroLookupAssumption = false

round807IntroducesEstimate : Bool
round807IntroducesEstimate = false

round807W2Closed : Bool
round807W2Closed = false

round807ClayPromotion : Bool
round807ClayPromotion = false

round807PZeroSelectedSelfForcingVanishesIsTrue :
  round807PZeroSelectedSelfForcingVanishes ≡ true
round807PZeroSelectedSelfForcingVanishesIsTrue = refl

round807PZeroSelfCommutatorVanishesIsTrue :
  round807PZeroSelfCommutatorVanishes ≡ true
round807PZeroSelfCommutatorVanishesIsTrue = refl

round807GlobalPZeroDefectVanishesIsTrue :
  round807GlobalPZeroDefectVanishes ≡ true
round807GlobalPZeroDefectVanishesIsTrue = refl

round807UsesMeanZeroLookupAssumptionIsFalse :
  round807UsesMeanZeroLookupAssumption ≡ false
round807UsesMeanZeroLookupAssumptionIsFalse = refl

round807IntroducesEstimateIsFalse :
  round807IntroducesEstimate ≡ false
round807IntroducesEstimateIsFalse = refl

round807W2ClosedIsFalse :
  round807W2Closed ≡ false
round807W2ClosedIsFalse = refl

round807ClayPromotionIsFalse :
  round807ClayPromotion ≡ false
round807ClayPromotionIsFalse = refl
