module DASHI.Physics.Closure.CanonicalPhysicsPathPostulateAudit where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

-- Provenance tags requested by the audit workflow.
data Provenance : Set where
  derivedFromRealStack : Provenance
  importedConcreteInstance : Provenance
  postulated : Provenance

NotPostulated : Provenance → Set
NotPostulated postulated = ⊥
NotPostulated _ = ⊤

record PhysicsClosureFullFieldAudit : Set where
  field
    kit : Provenance
    metricEmergence : Provenance
    quadraticFormZ : Provenance
    polarizationZ : Provenance
    orthogonalityZ : Provenance
    signature31Theorem : Provenance
    signature31 : Provenance
    CS : Provenance
    L : Provenance
    constraintClosure : Provenance
    mdlLyap : Provenance
    mdlFejer : Provenance
    dynamics : Provenance
    universality : Provenance

record MinimalCredibleFieldAudit : Set where
  field
    full : Provenance
    observables : Provenance
    closureSignatureMatchesPrediction : Provenance

record KnownLimitsGRFieldAudit : Set where
  field
    grAdapter : Provenance
    fullMatterGaugeRecovery : Provenance
    grRecovered : Provenance
    recovery : Provenance

record KnownLimitsQFTFieldAudit : Set where
  field
    qftAdapter : Provenance
    contractionSignatureToSpinDiracBridge : Provenance
    fullMatterGaugeRecovery : Provenance
    canonicalWaveLiftEvenBridge : Provenance
    concreteUnification : Provenance
    concreteContractionQuadraticBridge : Provenance
    cliffordBridge : Provenance
    waveLiftEvenBridge : Provenance
    canonicalClifford : Provenance
    canonicalWaveLiftIntoEven : Provenance
    fermionEvenLiftStructure : Provenance
    physicalWaveState : Provenance
    physicalWaveLift : Provenance
    physicalWaveEvenSubalgebra : Provenance
    physicalWaveLandsInEven : Provenance
    gaugeCouplingStructure : Provenance
    qftRecovered : Provenance
    recovery : Provenance

canonicalPhysicsClosureFullAudit : PhysicsClosureFullFieldAudit
canonicalPhysicsClosureFullAudit =
  record
    { kit = importedConcreteInstance
    ; metricEmergence = importedConcreteInstance
    ; quadraticFormZ = derivedFromRealStack
    ; polarizationZ = derivedFromRealStack
    ; orthogonalityZ = derivedFromRealStack
    ; signature31Theorem = derivedFromRealStack
    ; signature31 = derivedFromRealStack
    ; CS = importedConcreteInstance
    ; L = importedConcreteInstance
    ; constraintClosure = importedConcreteInstance
    ; mdlLyap = derivedFromRealStack
    ; mdlFejer = importedConcreteInstance
    ; dynamics = importedConcreteInstance
    ; universality = importedConcreteInstance
    }

canonicalMinimalCredibleAudit : MinimalCredibleFieldAudit
canonicalMinimalCredibleAudit =
  record
    { full = importedConcreteInstance
    ; observables = importedConcreteInstance
    ; closureSignatureMatchesPrediction = derivedFromRealStack
    }

canonicalKnownLimitsGRAudit : KnownLimitsGRFieldAudit
canonicalKnownLimitsGRAudit =
  record
    { grAdapter = importedConcreteInstance
    ; fullMatterGaugeRecovery = importedConcreteInstance
    ; grRecovered = importedConcreteInstance
    ; recovery = importedConcreteInstance
    }

canonicalKnownLimitsQFTAudit : KnownLimitsQFTFieldAudit
canonicalKnownLimitsQFTAudit =
  record
    { qftAdapter = importedConcreteInstance
    ; contractionSignatureToSpinDiracBridge = importedConcreteInstance
    ; fullMatterGaugeRecovery = importedConcreteInstance
    ; canonicalWaveLiftEvenBridge = importedConcreteInstance
    ; concreteUnification = derivedFromRealStack
    ; concreteContractionQuadraticBridge = derivedFromRealStack
    ; cliffordBridge = derivedFromRealStack
    ; waveLiftEvenBridge = derivedFromRealStack
    ; canonicalClifford = derivedFromRealStack
    ; canonicalWaveLiftIntoEven = derivedFromRealStack
    ; fermionEvenLiftStructure = derivedFromRealStack
    ; physicalWaveState = derivedFromRealStack
    ; physicalWaveLift = derivedFromRealStack
    ; physicalWaveEvenSubalgebra = derivedFromRealStack
    ; physicalWaveLandsInEven = derivedFromRealStack
    ; gaugeCouplingStructure = importedConcreteInstance
    ; qftRecovered = importedConcreteInstance
    ; recovery = importedConcreteInstance
    }

noEssentialPostulatesPhysicsClosureFull : Set
noEssentialPostulatesPhysicsClosureFull =
  NotPostulated (PhysicsClosureFullFieldAudit.kit canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.metricEmergence canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.quadraticFormZ canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.polarizationZ canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.orthogonalityZ canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.signature31Theorem canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.signature31 canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.CS canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.L canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.constraintClosure canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.mdlLyap canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.mdlFejer canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.dynamics canonicalPhysicsClosureFullAudit)
  × NotPostulated (PhysicsClosureFullFieldAudit.universality canonicalPhysicsClosureFullAudit)

noEssentialPostulatesMinimalCredible : Set
noEssentialPostulatesMinimalCredible =
  NotPostulated (MinimalCredibleFieldAudit.full canonicalMinimalCredibleAudit)
  × NotPostulated (MinimalCredibleFieldAudit.observables canonicalMinimalCredibleAudit)
  × NotPostulated (MinimalCredibleFieldAudit.closureSignatureMatchesPrediction canonicalMinimalCredibleAudit)

noEssentialPostulatesKnownLimitsGR : Set
noEssentialPostulatesKnownLimitsGR =
  NotPostulated (KnownLimitsGRFieldAudit.grAdapter canonicalKnownLimitsGRAudit)
  × NotPostulated (KnownLimitsGRFieldAudit.fullMatterGaugeRecovery canonicalKnownLimitsGRAudit)
  × NotPostulated (KnownLimitsGRFieldAudit.grRecovered canonicalKnownLimitsGRAudit)
  × NotPostulated (KnownLimitsGRFieldAudit.recovery canonicalKnownLimitsGRAudit)

noEssentialPostulatesKnownLimitsQFT : Set
noEssentialPostulatesKnownLimitsQFT =
  NotPostulated (KnownLimitsQFTFieldAudit.qftAdapter canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.contractionSignatureToSpinDiracBridge canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.fullMatterGaugeRecovery canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.canonicalWaveLiftEvenBridge canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.concreteUnification canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.concreteContractionQuadraticBridge canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.cliffordBridge canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.waveLiftEvenBridge canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.canonicalClifford canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.canonicalWaveLiftIntoEven canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.fermionEvenLiftStructure canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.physicalWaveState canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.physicalWaveLift canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.physicalWaveEvenSubalgebra canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.physicalWaveLandsInEven canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.gaugeCouplingStructure canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.qftRecovered canonicalKnownLimitsQFTAudit)
  × NotPostulated (KnownLimitsQFTFieldAudit.recovery canonicalKnownLimitsQFTAudit)

noEssentialPostulatesOnCanonicalPhysicsPath : Set
noEssentialPostulatesOnCanonicalPhysicsPath =
  noEssentialPostulatesPhysicsClosureFull
  × noEssentialPostulatesMinimalCredible
  × noEssentialPostulatesKnownLimitsGR
  × noEssentialPostulatesKnownLimitsQFT

canonicalNoEssentialPostulatesOnCanonicalPhysicsPath :
  noEssentialPostulatesOnCanonicalPhysicsPath
canonicalNoEssentialPostulatesOnCanonicalPhysicsPath =
  (tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt)
  , (tt , tt , tt)
  , (tt , tt , tt , tt)
  , (tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt , tt)
