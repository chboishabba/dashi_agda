{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SelfOrbitCommutatorCarrierRound713Exact where

------------------------------------------------------------------------
-- ROUND713 / COMPLETE R708 SELF ORBIT ON THE EXHAUSTIVE SELECTED-SELF
--            COMMUTATOR CARRIER
--
-- R712 proves pointwise, with the p=0 branch preserved exactly,
--
--   selfNestedCell(beta) = Self4*(beta),
--
-- where Self4* is four copies of the selected-self mixed commutator away from
-- p=0 and zero on the same exceptional branch.
--
-- Push that identity through the literal R708 consumer:
--
--   coherent spectator pairing
--     -> complete same-output spectator row
--     -> k=0 outer mask
--     -> three outer energy legs
--     -> complete physical-triad enumeration.
--
-- Hence the complete self contribution in the Clay-facing R700 orbit is
-- exactly one explicit scalar orbit built from the selected-self commutator.
-- No estimate and no cancellation claim is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovarianceWorkExact as Work
import DASHI.Physics.Closure.NSTriadKNFullSquareAsSpectatorRowsRound546Exact as R546
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650UnitNestedOrbitSelfExternalSplitRound708Exact as R708
import DASHI.Physics.Closure.NSTriadKNR650UnitSelfNestedCommutatorNormalFormRound712Exact as R712

module SelfOrbitCarrier
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

  module Split =
    R708.UnitOrbitSplit physicalSystem S L H velocityTransverse

  module Normal =
    R712.UnitSelfNormalForm physicalSystem S L H velocityTransverse

  commutatorPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  commutatorPair alpha beta =
    Work.coherentWork
      (Split.Full.Nested.Base.mixedCell alpha)
      (Normal.exhaustiveSelfCommutatorFourCopies beta)

  selfPairIsCommutatorPair :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Split.selfPair alpha beta ≡ commutatorPair alpha beta
  selfPairIsCommutatorPair alpha beta =
    cong
      (Work.coherentWork (Split.Full.Nested.Base.mixedCell alpha))
      (Normal.selfNestedCellIsExhaustiveFourSelfCommutators beta)

  commutatorOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  commutatorOuterRow beta =
    R546.spectatorRow commutatorPair beta
      (Split.Full.Nested.Base.fibre (Physical.k beta))

  rowTransport :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Split.selfPair beta items
    ≡ R546.spectatorRow commutatorPair beta items
  rowTransport beta [] = refl
  rowTransport beta (alpha ∷ rest) =
    cong₂ _+_
      (selfPairIsCommutatorPair alpha beta)
      (rowTransport beta rest)

  selfOuterRowIsCommutatorOuterRow :
    (beta : Physical.PhysicalTriadIncidence) →
    Split.selfOuterRow beta ≡ commutatorOuterRow beta
  selfOuterRowIsCommutatorOuterRow beta =
    rowTransport beta
      (Split.Full.Nested.Base.fibre (Physical.k beta))

  maskedCommutatorOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  maskedCommutatorOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = commutatorOuterRow beta

  maskedSelfOuterRowIsMaskedCommutatorOuterRow :
    (beta : Physical.PhysicalTriadIncidence) →
    Split.maskedSelfOuterRow beta ≡ maskedCommutatorOuterRow beta
  maskedSelfOuterRowIsMaskedCommutatorOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = refl
  ... | false = selfOuterRowIsCommutatorOuterRow beta

  commutatorOrbitResidue :
    Physical.PhysicalTriadIncidence → ℚ
  commutatorOrbitResidue beta =
    maskedCommutatorOuterRow beta
      + maskedCommutatorOuterRow (Orbit.pEnergyLeg beta)
      + maskedCommutatorOuterRow (Orbit.qEnergyLeg beta)

  selfOrbitResidueIsCommutatorOrbitResidue :
    (beta : Physical.PhysicalTriadIncidence) →
    Split.selfOrbitResidue beta ≡ commutatorOrbitResidue beta
  selfOrbitResidueIsCommutatorOrbitResidue beta =
    cong₂ _+_
      (cong₂ _+_
        (maskedSelfOuterRowIsMaskedCommutatorOuterRow beta)
        (maskedSelfOuterRowIsMaskedCommutatorOuterRow
          (Orbit.pEnergyLeg beta)))
      (maskedSelfOuterRowIsMaskedCommutatorOuterRow
        (Orbit.qEnergyLeg beta))

  foldCommutatorOrbit :
    List Physical.PhysicalTriadIncidence → ℚ
  foldCommutatorOrbit = R38.foldPower commutatorOrbitResidue

  foldSelfOrbitIsFoldCommutatorOrbit :
    (items : List Physical.PhysicalTriadIncidence) →
    Split.foldSelfOrbit items ≡ foldCommutatorOrbit items
  foldSelfOrbitIsFoldCommutatorOrbit [] = refl
  foldSelfOrbitIsFoldCommutatorOrbit (beta ∷ rest) =
    cong₂ _+_
      (selfOrbitResidueIsCommutatorOrbitResidue beta)
      (foldSelfOrbitIsFoldCommutatorOrbit rest)

  completeSelfOrbitIsCompleteCommutatorOrbit :
    Split.foldSelfOrbit
      (Physical.physicalTriadEnumeration Split.Full.Nested.Base.cutoff)
    ≡
    foldCommutatorOrbit
      (Physical.physicalTriadEnumeration Split.Full.Nested.Base.cutoff)
  completeSelfOrbitIsCompleteCommutatorOrbit =
    foldSelfOrbitIsFoldCommutatorOrbit
      (Physical.physicalTriadEnumeration Split.Full.Nested.Base.cutoff)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round713CompleteSelfOrbitOnSelectedSelfCommutatorCarrier : Bool
round713CompleteSelfOrbitOnSelectedSelfCommutatorCarrier = true

round713ZeroBranchesPreservedExactly : Bool
round713ZeroBranchesPreservedExactly = true

round713SelfOrbitExactCancellationClosed : Bool
round713SelfOrbitExactCancellationClosed = false

round713IntroducesEstimate : Bool
round713IntroducesEstimate = false

round713ClayPromotion : Bool
round713ClayPromotion = false

round713CompleteSelfOrbitOnSelectedSelfCommutatorCarrierIsTrue :
  round713CompleteSelfOrbitOnSelectedSelfCommutatorCarrier ≡ true
round713CompleteSelfOrbitOnSelectedSelfCommutatorCarrierIsTrue = refl

round713ZeroBranchesPreservedExactlyIsTrue :
  round713ZeroBranchesPreservedExactly ≡ true
round713ZeroBranchesPreservedExactlyIsTrue = refl

round713SelfOrbitExactCancellationClosedIsFalse :
  round713SelfOrbitExactCancellationClosed ≡ false
round713SelfOrbitExactCancellationClosedIsFalse = refl

round713IntroducesEstimateIsFalse :
  round713IntroducesEstimate ≡ false
round713IntroducesEstimateIsFalse = refl

round713ClayPromotionIsFalse :
  round713ClayPromotion ≡ false
round713ClayPromotionIsFalse = refl
