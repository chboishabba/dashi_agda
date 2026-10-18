{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650UnitNestedOrbitSelfExternalSplitRound708Exact where

------------------------------------------------------------------------
-- ROUND708 / THE ACTUAL R700 UNIT-WEIGHT ORBIT = SELF + EXTERNAL
--
-- R703--R707 force the historical self/external distinction back into the
-- current Clay-facing calculation for one precise reason: the selected self
-- inner interaction has canonical mates under the three outer energy legs,
-- whereas a generic external inner interaction does not.
--
-- Use R613 at R694's UNIT weight, on the exact same physical system as R700:
--
--   Nested_beta = Self_beta + External_beta.
--
-- Push this equality through
--
--   * the R700 spectator coherent pairing,
--   * the complete same-output spectator row,
--   * R700's zero-output scalar mask,
--   * the three outer energy legs,
--   * the complete physical triad enumeration.
--
-- Result:
--
--   NestedOrbit = SelfOrbit + ExternalOrbit
--
-- pointwise and globally, before any norm or estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
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
import DASHI.Physics.Closure.NSTriadKNR573SelfExternalNestedCompanionSplitRound613Exact as R613
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650NestedFourHelicityTriadOrbitRound700Exact as R700

module UnitOrbitSplit
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

  system = Field30.finiteSystem physicalSystem

  module Full =
    R700.NestedOrbit physicalSystem S L H velocityTransverse

  module Split =
    R613.NestedNetworkSplit
      R694.unitWeight S L H system velocityTransverse

  selfNestedCell externalNestedCell :
    Physical.PhysicalTriadIncidence → C3.Complex3 R694.F
  selfNestedCell = Split.selfNestedWeightedCompanionCell
  externalNestedCell = Split.externalNestedWeightedCompanionCell

  nestedCellSplits :
    (beta : Physical.PhysicalTriadIncidence) →
    Full.Nested.nestedCell beta
    ≡ C3.complex3Add (selfNestedCell beta) (externalNestedCell beta)
  nestedCellSplits beta =
    Split.nestedWeightedCompanionSplitsSelfExternal beta

  selfPair externalPair :
    Physical.PhysicalTriadIncidence →
    Physical.PhysicalTriadIncidence → ℚ
  selfPair alpha beta =
    Work.coherentWork
      (Full.Nested.Base.mixedCell alpha)
      (selfNestedCell beta)
  externalPair alpha beta =
    Work.coherentWork
      (Full.Nested.Base.mixedCell alpha)
      (externalNestedCell beta)

  nestedPairSplits :
    (alpha beta : Physical.PhysicalTriadIncidence) →
    Full.Nested.nestedPair alpha beta
    ≡ selfPair alpha beta + externalPair alpha beta
  nestedPairSplits alpha beta =
    trans
      (cong
        (Work.coherentWork (Full.Nested.Base.mixedCell alpha))
        (nestedCellSplits beta))
      (Work.workAddRight
        (Full.Nested.Base.mixedCell alpha)
        (selfNestedCell beta)
        (externalNestedCell beta))

  selfOuterRow externalOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  selfOuterRow beta =
    R546.spectatorRow selfPair beta
      (Full.Nested.Base.fibre (Physical.k beta))
  externalOuterRow beta =
    R546.spectatorRow externalPair beta
      (Full.Nested.Base.fibre (Physical.k beta))

  rowSplitOn :
    (beta : Physical.PhysicalTriadIncidence) →
    (items : List Physical.PhysicalTriadIncidence) →
    R546.spectatorRow Full.Nested.nestedPair beta items
    ≡
    R546.spectatorRow selfPair beta items
      + R546.spectatorRow externalPair beta items
  rowSplitOn beta [] = refl
  rowSplitOn beta (alpha ∷ rest) =
    trans
      (cong₂ _+_
        (nestedPairSplits alpha beta)
        (rowSplitOn beta rest))
      (solve
        ( selfPair alpha beta
        ∷ externalPair alpha beta
        ∷ R546.spectatorRow selfPair beta rest
        ∷ R546.spectatorRow externalPair beta rest
        ∷ []))

  nestedOuterRowSplits :
    (beta : Physical.PhysicalTriadIncidence) →
    Full.nestedOuterRow beta
    ≡ selfOuterRow beta + externalOuterRow beta
  nestedOuterRowSplits beta =
    rowSplitOn beta (Full.Nested.Base.fibre (Physical.k beta))

  maskedSelfOuterRow maskedExternalOuterRow :
    Physical.PhysicalTriadIncidence → ℚ
  maskedSelfOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = selfOuterRow beta

  maskedExternalOuterRow beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = 0ℚ
  ... | false = externalOuterRow beta

  maskedNestedOuterRowSplits :
    (beta : Physical.PhysicalTriadIncidence) →
    Full.maskedNestedOuterRow beta
    ≡ maskedSelfOuterRow beta + maskedExternalOuterRow beta
  maskedNestedOuterRowSplits beta
    with Output.modeEqual (Physical.k beta) Z3.zeroMode
  ... | true = refl
  ... | false = nestedOuterRowSplits beta

  selfOrbitResidue externalOrbitResidue :
    Physical.PhysicalTriadIncidence → ℚ
  selfOrbitResidue beta =
    maskedSelfOuterRow beta
      + maskedSelfOuterRow (Orbit.pEnergyLeg beta)
      + maskedSelfOuterRow (Orbit.qEnergyLeg beta)

  externalOrbitResidue beta =
    maskedExternalOuterRow beta
      + maskedExternalOuterRow (Orbit.pEnergyLeg beta)
      + maskedExternalOuterRow (Orbit.qEnergyLeg beta)

  nestedOrbitResidueSplits :
    (beta : Physical.PhysicalTriadIncidence) →
    Full.nestedTriadOrbitResidue beta
    ≡ selfOrbitResidue beta + externalOrbitResidue beta
  nestedOrbitResidueSplits beta =
    trans
      (cong₂ _+_
        (cong₂ _+_
          (maskedNestedOuterRowSplits beta)
          (maskedNestedOuterRowSplits (Orbit.pEnergyLeg beta)))
        (maskedNestedOuterRowSplits (Orbit.qEnergyLeg beta)))
      (solve
        ( maskedSelfOuterRow beta
        ∷ maskedExternalOuterRow beta
        ∷ maskedSelfOuterRow (Orbit.pEnergyLeg beta)
        ∷ maskedExternalOuterRow (Orbit.pEnergyLeg beta)
        ∷ maskedSelfOuterRow (Orbit.qEnergyLeg beta)
        ∷ maskedExternalOuterRow (Orbit.qEnergyLeg beta)
        ∷ []))

  foldSelfOrbit foldExternalOrbit :
    List Physical.PhysicalTriadIncidence → ℚ
  foldSelfOrbit = R38.foldPower selfOrbitResidue
  foldExternalOrbit = R38.foldPower externalOrbitResidue

  foldOrbitSplits :
    (items : List Physical.PhysicalTriadIncidence) →
    R38.foldPower Full.nestedTriadOrbitResidue items
    ≡ foldSelfOrbit items + foldExternalOrbit items
  foldOrbitSplits [] = refl
  foldOrbitSplits (beta ∷ rest) =
    trans
      (cong₂ _+_
        (nestedOrbitResidueSplits beta)
        (foldOrbitSplits rest))
      (solve
        ( selfOrbitResidue beta
        ∷ externalOrbitResidue beta
        ∷ foldSelfOrbit rest
        ∷ foldExternalOrbit rest
        ∷ []))

  completeNestedOrbitSplitsSelfExternal :
    R38.foldPower Full.nestedTriadOrbitResidue
      (Physical.physicalTriadEnumeration Full.Nested.Base.cutoff)
    ≡
    foldSelfOrbit
      (Physical.physicalTriadEnumeration Full.Nested.Base.cutoff)
    +
    foldExternalOrbit
      (Physical.physicalTriadEnumeration Full.Nested.Base.cutoff)
  completeNestedOrbitSplitsSelfExternal =
    foldOrbitSplits
      (Physical.physicalTriadEnumeration Full.Nested.Base.cutoff)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round708R700UnitNestedCellSelfExternalSplitClosed : Bool
round708R700UnitNestedCellSelfExternalSplitClosed = true

round708R700MaskedOrbitSelfExternalSplitClosed : Bool
round708R700MaskedOrbitSelfExternalSplitClosed = true

round708R700CompleteOrbitSelfExternalSplitClosed : Bool
round708R700CompleteOrbitSelfExternalSplitClosed = true

round708SelfOrbitExactCancellationClosed : Bool
round708SelfOrbitExactCancellationClosed = false

round708ExternalOrbitCutoffUniformSignedPaymentClosed : Bool
round708ExternalOrbitCutoffUniformSignedPaymentClosed = false

round708IntroducesEstimate : Bool
round708IntroducesEstimate = false

round708ClayPromotion : Bool
round708ClayPromotion = false

round708R700CompleteOrbitSelfExternalSplitClosedIsTrue :
  round708R700CompleteOrbitSelfExternalSplitClosed ≡ true
round708R700CompleteOrbitSelfExternalSplitClosedIsTrue = refl

round708SelfOrbitExactCancellationClosedIsFalse :
  round708SelfOrbitExactCancellationClosed ≡ false
round708SelfOrbitExactCancellationClosedIsFalse = refl

round708ExternalOrbitCutoffUniformSignedPaymentClosedIsFalse :
  round708ExternalOrbitCutoffUniformSignedPaymentClosed ≡ false
round708ExternalOrbitCutoffUniformSignedPaymentClosedIsFalse = refl

round708IntroducesEstimateIsFalse :
  round708IntroducesEstimate ≡ false
round708IntroducesEstimateIsFalse = refl

round708ClayPromotionIsFalse :
  round708ClayPromotion ≡ false
round708ClayPromotionIsFalse = refl
