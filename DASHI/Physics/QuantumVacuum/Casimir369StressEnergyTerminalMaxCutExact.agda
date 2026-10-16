module DASHI.Physics.QuantumVacuum.Casimir369StressEnergyTerminalMaxCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.QuantumVacuum.Casimir369HyperfabricCommutationExact as Hyper
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress3
import DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact as EC
import DASHI.Physics.QuantumVacuum.CasimirSetoidFullStressSameObjectExact as Stress4
import DASHI.Physics.QuantumVacuum.CasimirQuantumInequalityBoundaryExact as QI
import DASHI.Physics.QuantumVacuum.CasimirGRNullFocusingBridgeExact as GR
import DASHI.Physics.QuantumVacuum.CasimirSetoidAnalyticScalarExact as Setoid
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Kernel
import DASHI.Physics.QuantumVacuum.PhysicalQuantities as Q

------------------------------------------------------------------------
-- TERMINAL CASIMIR / 369 / STRESS-ENERGY MAX-CUT
--
-- This is a status/consumer owner, not another physical mechanism.  It marks
-- which internal structural and QFT theorem families are now owned and names
-- the first genuinely same-object payments that remain.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Typed terminal witnesses for each still-live external/same-object cut.
------------------------------------------------------------------------

record CanonicalSetoidScalePayment : Set₁ where
  field
    authority : Setoid.BishopCasimirSetoidAuthority
    separation : Q.Length
    scaleWitness :
      Stress4.CasimirSetoidScaleWitness
        (Setoid.model authority)
        separation
    reading : String

open CanonicalSetoidScalePayment public

record SameObjectQuantumInequalityPayment : Set₁ where
  field
    prescription : QI.CasimirQuantumInequalityPrescription
    sameStressObjectAsCasimirSetoidReconstruction : Set
    theoremAppliesToSelectedBackground : Set
    reading : String

open SameObjectQuantumInequalityPayment public

record SameObjectANECApplication : Set₁ where
  field
    prescription : QI.CasimirANECNullCurvePrescription
    sameStressObjectAsCasimirSetoidReconstruction : Set
    averagedIntegralVerdict : Set
    reading : String

open SameObjectANECApplication public

record SameObjectSemiclassicalGravityPayment : Set₁ where
  field
    kernel : Kernel.CasimirScalarModel
    separation : Q.Length
    gravitationalWeld : GR.CasimirSemiclassicalGravityWeld kernel separation
    fullRenormalizedStressSameObject : Set
    metricOrCurvatureResponse : Set
    calibratedBackreaction : Set
    reading : String

open SameObjectSemiclassicalGravityPayment public

------------------------------------------------------------------------
-- 2. Terminal boundary: what is actually paid now.
------------------------------------------------------------------------

record Casimir369StressEnergyTerminalBoundary : Set where
  constructor casimir-369-stress-energy-terminal-boundary
  field
    finite369StructurePaid : Bool
    coefficientLatticePaid : Bool
    physicalSO3StressContractionPaid : Bool
    localQFTStressPaid : Bool
    normalizedFull4x4StressPaid : Bool
    arbitraryNullDirectionFormulaPaid : Bool
    pointwiseEnergyConditionFingerprintPaid : Bool
    setoidFullStressInterfacePaid : Bool
    brownMaclaySourceAuthorityPaid : Bool
    fordRomanQISourceAuthorityPaid : Bool
    grNECNullConvergenceFirewallPaid : Bool

    concreteCanonicalSetoidScaleWitnessPaid : Bool
    legacyPropositionalQuotientPaid : Bool
    sameObjectQuantumInequalityPaid : Bool
    sameObjectANECApplicationPaid : Bool
    semiclassicalGravityBackreactionPaid : Bool
    directStressMeasurementPaid : Bool
    macroscopicNegativeEnergyEngineeringPaid : Bool

open Casimir369StressEnergyTerminalBoundary public

canonicalTerminalBoundary : Casimir369StressEnergyTerminalBoundary
canonicalTerminalBoundary =
  casimir-369-stress-energy-terminal-boundary
    true true true true true true true true true true true
    false false false false false false false

------------------------------------------------------------------------
-- 3. Existing owners witness the paid side rather than booleans floating free.
------------------------------------------------------------------------

hyperfabricBoundaryWitness : Hyper.Casimir369HyperfabricBoundary
hyperfabricBoundaryWitness = Hyper.canonicalCasimir369HyperfabricBoundary

stressContractionBoundaryWitness : Stress3.CasimirSO3StressMaxCutBoundary
stressContractionBoundaryWitness = Stress3.canonicalCasimirSO3StressMaxCutBoundary

energyConditionBoundaryWitness : EC.CasimirBrownMaclayEnergyConditionBoundary
energyConditionBoundaryWitness = EC.canonicalCasimirBrownMaclayEnergyConditionBoundary

setoidStressBoundaryWitness : Stress4.CasimirSetoidFullStressBoundary
setoidStressBoundaryWitness = Stress4.canonicalCasimirSetoidFullStressBoundary

quantumInequalityBoundaryWitness : QI.CasimirQuantumInequalityBoundary
quantumInequalityBoundaryWitness = QI.canonicalCasimirQuantumInequalityBoundary

gravityBoundaryWitness : GR.CasimirGRNullFocusingBoundary
gravityBoundaryWitness = GR.canonicalCasimirGRNullFocusingBoundary

------------------------------------------------------------------------
-- 4. No more numerology as payment.
------------------------------------------------------------------------

data FurtherCardinalityFactorisationCountsAsPhysicalPayment : Set where
data PointwiseViolationCountsAsAveragedViolationPayment : Set where
data TheoryStressCountsAsMeasuredGravityPayment : Set where

furtherCardinalityIsNotPayment :
  FurtherCardinalityFactorisationCountsAsPhysicalPayment → ⊥
furtherCardinalityIsNotPayment ()

pointwiseIsNotAveragedPayment :
  PointwiseViolationCountsAsAveragedViolationPayment → ⊥
pointwiseIsNotAveragedPayment ()

theoryStressIsNotGravityMeasurement :
  TheoryStressCountsAsMeasuredGravityPayment → ⊥
theoryStressIsNotGravityMeasurement ()

------------------------------------------------------------------------
-- 5. Machine-readable first-blocker ordering.
------------------------------------------------------------------------

data RemainingCasimirStressEnergyBlocker : Set where
  missingConcreteCanonicalSetoidAuthorityAndScaleWitness : RemainingCasimirStressEnergyBlocker
  missingOptionalLegacyQuotient : RemainingCasimirStressEnergyBlocker
  missingSpecifiedQISamplingApplication : RemainingCasimirStressEnergyBlocker
  missingSpecifiedANECApplication : RemainingCasimirStressEnergyBlocker
  missingSemiclassicalGravitySameObjectWeld : RemainingCasimirStressEnergyBlocker
  missingDirectStressOrGravityMeasurement : RemainingCasimirStressEnergyBlocker
  missingExactHeadKernelReceipt : RemainingCasimirStressEnergyBlocker

firstMathematicalSameObjectBlocker : RemainingCasimirStressEnergyBlocker
firstMathematicalSameObjectBlocker =
  missingConcreteCanonicalSetoidAuthorityAndScaleWitness

firstAveragedConditionBlocker : RemainingCasimirStressEnergyBlocker
firstAveragedConditionBlocker = missingSpecifiedQISamplingApplication

firstGravityBlocker : RemainingCasimirStressEnergyBlocker
firstGravityBlocker = missingSemiclassicalGravitySameObjectWeld

firstExperimentalBlocker : RemainingCasimirStressEnergyBlocker
firstExperimentalBlocker = missingDirectStressOrGravityMeasurement

terminalReading : String
terminalReading =
  "The internal finite 369/SO3 carrier work, spatial 9->3->1 stress contraction, Brown-Maclay normalized 4x4 stress fingerprint, arbitrary-direction pointwise NEC formula, local WEC/SEC/DEC verdicts, setoid-native full-stress interface, Ford-Roman QI provenance and GR NEC/null-convergence firewall are paid. The first remaining mathematical same-object payment is an inhabited BishopCasimirSetoidAuthority together with a positive Casimir scale witness on that authority's model at one separation. QI/ANEC then require explicit averaging prescriptions; GR requires a same-object semiclassical Einstein/conservation/curvature solution; experiment requires direct stress/gravity measurement. Further 3/6/9/18/27 factorisation is not payment."
