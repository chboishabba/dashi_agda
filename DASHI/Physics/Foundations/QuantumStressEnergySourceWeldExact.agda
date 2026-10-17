module DASHI.Physics.Foundations.QuantumStressEnergySourceWeldExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.List.Base using ([]; _∷_)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Physics.Foundations.QuantumStressEnergyEngineeringBridgeExact as Bridge
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir

------------------------------------------------------------------------
-- SOURCE-BOUNDED QUANTUM-STRESS WELD
--
-- Brown-Maclay pays a renormalized parallel-plate electromagnetic stress-
-- energy calculation. Ford/Roman pay quantum-inequality / averaged-condition
-- restrictions at their stated scope. Neither source measures GR backreaction
-- from a Casimir apparatus or supplies a warp/wormhole engineering receipt.
------------------------------------------------------------------------

brownMaclay1969 : Attribution.AttributedSource
brownMaclay1969 =
  Attribution.mkDOISource
    "Lowell S. Brown and G. Jordan Maclay"
    "Vacuum Stress between Conducting Plates: An Image Solution"
    "Physical Review 184, 1272-1279"
    "1969"
    "10.1103/PhysRev.184.1272"
    "https://doi.org/10.1103/PhysRev.184.1272"
    Attribution.academicArticleSource
    "source for the finite electromagnetic stress-energy tensor between ideal conducting parallel plates at zero and finite temperature; not a measurement of gravitational backreaction"
    Attribution.publicAttribution

fordRoman1995 : Attribution.AttributedSource
fordRoman1995 =
  Attribution.mkDOISource
    "L. H. Ford and Thomas A. Roman"
    "Averaged energy conditions and quantum inequalities"
    "Physical Review D 51, 4277"
    "1995"
    "10.1103/PhysRevD.51.4277"
    "https://doi.org/10.1103/PhysRevD.51.4277"
    Attribution.academicArticleSource
    "source for relations among averaged energy conditions and quantum inequalities, including the importance of the Casimir-vacuum background in difference inequalities; not a generic engineering licence for negative energy"
    Attribution.publicAttribution

fordRoman1997 : Attribution.AttributedSource
fordRoman1997 =
  Attribution.mkDOISource
    "L. H. Ford and Thomas A. Roman"
    "Restrictions on negative energy density in flat spacetime"
    "Physical Review D 55, 2082"
    "1997"
    "10.1103/PhysRevD.55.2082"
    "https://doi.org/10.1103/PhysRevD.55.2082"
    Attribution.academicArticleSource
    "source for quantum-inequality bounds on negative energy density, including electromagnetic-field bounds in flat spacetime; scope does not automatically identify a Casimir engineering protocol"
    Attribution.publicAttribution

quantumStressSourceAtlas : Attribution.AttributedSourceAtlas
quantumStressSourceAtlas =
  Attribution.mkSourceAtlas
    "parallel-plate quantum stress and quantum-inequality source atlas"
    "DASHI.Physics.Foundations.QuantumStressEnergySourceWeldExact"
    (brownMaclay1969 ∷ fordRoman1995 ∷ fordRoman1997 ∷ [])
    "source-bounded theory payments only; measured Casimir force, measured stress-energy, macroscopic scaling, metric response and warp/wormhole capability remain distinct consumers"

record ParallelPlateStressSource : Set where
  constructor parallel-plate-stress-source
  field
    idealParallelPlateKernelReference : String
    renormalizedStressTensorReference : String
    finiteStressTensorCalculated : Bool
    stressTensorIsQFTTheoryObject : Bool
    sameObjectStressTensorDirectlyMeasured : Bool
    gravitationalBackreactionMeasured : Bool

open ParallelPlateStressSource public

canonicalBrownMaclayStressSource : ParallelPlateStressSource
canonicalBrownMaclayStressSource =
  parallel-plate-stress-source
    "DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel"
    "Brown and Maclay 1969, DOI 10.1103/PhysRev.184.1272"
    true
    true
    false
    false

record QuantumStressSourcePayment : Set where
  constructor quantum-stress-source-payment
  field
    qftExpectationTheoryPaid : Bool
    finiteRenormalizedStressTheoryPaid : Bool
    quantumInequalityLiteraturePaid : Bool
    backgroundVacuumQualificationPaid : Bool
    sameObjectRenormalizedStressMeasured : Bool
    macroscopicControlledScalingPaid : Bool
    measuredGravitationalBackreactionPaid : Bool
    warpOrWormholePhysicalSourcePaid : Bool

open QuantumStressSourcePayment public

canonicalQuantumStressSourcePayment : QuantumStressSourcePayment
canonicalQuantumStressSourcePayment =
  quantum-stress-source-payment
    true true true true false false false false

record QuantumStressSourceWeld : Set where
  constructor quantum-stress-source-weld
  field
    engineeringRoute : Bridge.QuantumStressEngineeringChain
    engineeringPhysicalPayment : Bridge.QuantumStressPaymentLedger
    sourcePayment : QuantumStressSourcePayment
    casimirKernelReference : String
    sourcePaymentDoesNotMutatePhysicalPaymentLedger : Bool

open QuantumStressSourceWeld public

canonicalQuantumStressSourceWeld : QuantumStressSourceWeld
canonicalQuantumStressSourceWeld =
  quantum-stress-source-weld
    Bridge.canonicalQuantumStressEngineeringChain
    Bridge.canonicalQuantumStressPaymentLedger
    canonicalQuantumStressSourcePayment
    "DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel"
    true

record QuantumStressSourceBoundary : Set where
  constructor quantum-stress-source-boundary
  field
    casimirForceDoesNotMeasureGravity : Bool
    qftStressCalculationDoesNotMeasureStressTensor : Bool
    quantumInequalityMustRespectBackgroundVacuum : Bool
    theoryPaymentDoesNotPayMacroscopicScaling : Bool
    macroscopicScalingDoesNotPayMeasuredBackreaction : Bool
    measuredBackreactionWouldStillNotByItselfPayWarpCapability : Bool
    siblingCasimir369StructureDoesNotTransferGravityMechanism : Bool

open QuantumStressSourceBoundary public

canonicalQuantumStressSourceBoundary : QuantumStressSourceBoundary
canonicalQuantumStressSourceBoundary =
  quantum-stress-source-boundary true true true true true true true
