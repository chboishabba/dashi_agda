{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SeparatedPZeroAlgebraicEliminationRound809Exact where

------------------------------------------------------------------------
-- ROUND809 / THE R804 p=0 "PROVENANCE DEFECT" VANISHES ALGEBRAICALLY
--
-- R804 conservatively isolates a branch supported on
--
--   ccTouched beta = false,   p_beta = 0.
--
-- No canonical u(0) provenance weld is actually needed.  The selected-self
-- p-forcing is the symmetrised ordered-pair interaction on pEnergyLeg beta.
-- If p_beta = 0, that leg has output zero.  R436 kills both selected ordered
-- terms from all-mode transversality alone, hence SelfP(beta)=0.  R437 then
-- kills the corresponding mixed-helicity commutator from its zero forcing
-- p-slot.
--
-- Therefore the exact R804 p=0 defect cell, every fixed-output fold, every
-- selected coherent-work term, and the global defect work are all zero.
--
-- No statement about the off-support velocity lookup u(0), no estimate, norm,
-- absolute value, or foreign carrier is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNMixedHelicityFixedOutputSwapRound224Exact as R224
import DASHI.Physics.Closure.NSTriadKNMixedHelicityForcingSwapRound230Exact as R230
import DASHI.Physics.Closure.NSTriadKNPhysicalSelectedTriadNetworkSplitRound95Exact as R95
import DASHI.Physics.Closure.NSTriadKNExternalOutputFibreSelfOrbitRemovalRound111Exact as R111
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityZeroOutputRound436Exact as R436
import DASHI.Physics.Closure.NSTriadKNProjectedForcingOuterCellExhaustiveRound437Exact as R437
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullGramCoherentFoldRound597Exact as R597
import DASHI.Physics.Closure.NSTriadKNR650OrbitProfileTwoFamilyResidualRound781Exact as R781
import DASHI.Physics.Closure.NSTriadKNR650SeparatedSelfZeroSafeSplitRound804Exact as R804

module SeparatedPZeroElimination
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

  selectedSelfPForcingZeroAtPZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.p beta ≡ Z3.zeroMode →
    R95.selfForcingP system beta
    ≡ C3.complex3Zero R804.R803.R802.F
  selectedSelfPForcingZeroAtPZero beta pZero =
    let
      leg = Orbit.pEnergyLeg beta

      legOutputZero :
        Physical.k leg ≡ Z3.zeroMode
      legOutputZero =
        trans (Orbit.pEnergyLegOutput beta) pZero

      swapOutputZero :
        Physical.k (Symmetry.swapTriad leg) ≡ Z3.zeroMode
      swapOutputZero =
        trans (Symmetry.swapTriadK leg) legOutputZero

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
          (Symmetry.swapTriad leg) swapOutputZero
    in
    trans
      (R111.selfForcingKIsTwoSelectedOrderedTerms system leg)
      (trans
        (cong₂ C3.complex3Add firstZero secondZero)
        (R230.complex3AddZeroLeft
          (C3.complex3Zero R804.R803.R802.F)))

  selectedSelfCommutatorZeroAtPZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Physical.p beta ≡ Z3.zeroMode →
    Sep.Sep.Self.selfCommutatorCell beta
    ≡ C3.complex3Zero R804.R803.R802.F
  selectedSelfCommutatorZeroAtPZero beta pZero =
    R437.forcingCommutatorZeroFromForcingZero
      S velocity
      (λ _ → R95.selfForcingP system beta)
      beta
      (selectedSelfPForcingZeroAtPZero beta pZero)

  pZeroDefectPointwiseZero :
    (beta : Physical.PhysicalTriadIncidence) →
    Sep.pZeroSelfDefect beta
    ≡ C3.complex3Zero R804.R803.R802.F
  pZeroDefectPointwiseZero beta
    with R781.ccTouched beta
       | Output.modeEqual (Physical.p beta) Z3.zeroMode in pDecision
  ... | true | decision = refl
  ... | false | true =
    selectedSelfCommutatorZeroAtPZero
      beta (Output.modeEqualSound pDecision)
  ... | false | false = refl

  pZeroDefectFoldZero :
    (output : Z3.FourierMode) →
    Sep.pZeroDefectFold output
    ≡ C3.complex3Zero R804.R803.R802.F
  pZeroDefectFoldZero output =
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
          (pZeroDefectPointwiseZero beta)
          (go rest))
        (R230.complex3AddZeroLeft
          (C3.complex3Zero R804.R803.R802.F))

  outputPZeroDefectWorkZero :
    (output : Z3.FourierMode) →
    Sep.outputPZeroDefectWork output ≡ 0ℚ
  outputPZeroDefectWorkZero output =
    trans
      (cong
        (Work.coherentWork (Sep.Sep.Split.Id.mixedFold output))
        (pZeroDefectFoldZero output))
      (R597.workZeroRight
        (Sep.Sep.Split.Id.mixedFold output))

  selectedPZeroDefectWorkZero :
    (output : Z3.FourierMode) →
    Sep.selectedPZeroDefectWork output ≡ 0ℚ
  selectedPZeroDefectWorkZero output
    with Output.modeEqual output Z3.zeroMode
  ... | true = refl
  ... | false = outputPZeroDefectWorkZero output

  sumPZeroDefectWorkZero :
    (outputs : List Z3.FourierMode) →
    Sep.sumPZeroDefectWork outputs ≡ 0ℚ
  sumPZeroDefectWorkZero [] = refl
  sumPZeroDefectWorkZero (output ∷ rest) =
    trans
      (cong₂ _+_
        (selectedPZeroDefectWorkZero output)
        (sumPZeroDefectWorkZero rest))
      (solve [])

  globalPZeroSelfDefectWorkZero :
    Sep.globalPZeroSelfDefectWork ≡ 0ℚ
  globalPZeroSelfDefectWorkZero =
    sumPZeroDefectWorkZero (Cube.cutoffModes cutoff)

round809PZeroSelectedSelfForcingVanishes : Bool
round809PZeroSelectedSelfForcingVanishes = true

round809PZeroSelfCommutatorVanishes : Bool
round809PZeroSelfCommutatorVanishes = true

round809PZeroDefectClosedAlgebraically : Bool
round809PZeroDefectClosedAlgebraically = true

round809UsesCanonicalZeroModeVelocity : Bool
round809UsesCanonicalZeroModeVelocity = false

round809IntroducesEstimate : Bool
round809IntroducesEstimate = false

round809W2Closed : Bool
round809W2Closed = false

round809ClayPromotion : Bool
round809ClayPromotion = false

round809PZeroDefectClosedAlgebraicallyIsTrue :
  round809PZeroDefectClosedAlgebraically ≡ true
round809PZeroDefectClosedAlgebraicallyIsTrue = refl

round809UsesCanonicalZeroModeVelocityIsFalse :
  round809UsesCanonicalZeroModeVelocity ≡ false
round809UsesCanonicalZeroModeVelocityIsFalse = refl

round809IntroducesEstimateIsFalse :
  round809IntroducesEstimate ≡ false
round809IntroducesEstimateIsFalse = refl

round809W2ClosedIsFalse :
  round809W2Closed ≡ false
round809W2ClosedIsFalse = refl

round809ClayPromotionIsFalse :
  round809ClayPromotion ≡ false
round809ClayPromotionIsFalse = refl
