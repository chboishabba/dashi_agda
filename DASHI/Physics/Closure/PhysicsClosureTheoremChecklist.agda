module DASHI.Physics.Closure.PhysicsClosureTheoremChecklist where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.ProjectionDefectToParallelogram as PDP
open import DASHI.Physics.QuadraticEmergenceShiftInstance as QES
open import DASHI.Geometry.ProjectionDefectSplitForcesParallelogram as PDSP
open import DASHI.Physics.Closure.ContractionForcesQuadraticTheorem as CFQT
open import DASHI.Physics.Closure.ContractionForcesQuadraticStrong as CFQS
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB
open import DASHI.Physics.Closure.QuadraticToCliffordBridgeTheorem as QTCB
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CEW
open import DASHI.Physics.Closure.PhysicsClosureCoreWitness as PCCW
open import DASHI.Physics.Closure.PhysicsClosureConstructorTheorem as PCCT
open import DASHI.Physics.Closure.PhysicsClosureRealizationIndependenceTheorem as PCRIT
open import DASHI.Physics.Closure.PhysicsClosureTheoremLadder as PCTL
open import DASHI.Physics.Closure.PhysicsClosureFull as PCF
open import DASHI.Physics.Closure.PhysicsClosureFullInstance as PCFI

record PhysicsClosureTheoremChecklist : Setω where
  field
    projectionDefectSplitForcesParallelogram :
      ∀ {m : Nat} →
      PDP.ProjectionDefectParallelogramPackage
        (QES.AdditiveVecℤ {m}) QES.ScalarFieldℤ

    parallelogramForcesQuadratic :
      CFQT.ContractionForcesQuadraticTheorem

    strongContractionNormalizesQuadratic :
      CFQS.ContractionForcesQuadraticStrong

    normalizedQuadraticForcesLorentzSignature :
      CQSB.ContractionQuadraticToSignatureBridgeTheorem

    lorentzSignatureForcesClifford :
      QTCB.QuadraticToCliffordBridgeTheorem

    lorentzSignatureForcesSpinDirac :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem

    waveLiftFactorsThroughEvenClifford :
      CEW.CliffordToEvenWaveLiftBridgeTheorem

    closureCoreWitnessForcesFullClosure :
      PCCT.PhysicsClosureConstructorTheorem

    canonicalCoreWitness :
      PCCW.PhysicsClosureCoreWitness

    canonicalFullClosure :
      PCF.PhysicsClosureFull

record PhysicsClosureHeadlineTheorem : Setω where
  field
    canonicalChecklist : PhysicsClosureTheoremChecklist
    shiftWitness : PCCW.PhysicsClosureCoreWitness
    shiftConstructorTheorem : PCCT.PhysicsClosureConstructorTheorem

record PhysicsClosureRealizationIndependenceChecklist : Setω where
  field
    canonicalHeadline : PhysicsClosureHeadlineTheorem
    independenceTheorem :
      PCRIT.PhysicsClosureRealizationIndependenceTheorem

record PhysicsClosureNamedTheoremChecklist : Setω where
  field
    theoremA :
      PCTL.ProjectionDefectSplitForcesParallelogramTheorem
    theoremB :
      PCTL.ParallelogramForcesQuadraticFormTheorem
    theoremC :
      PCTL.StrongContractionNormalizesQuadraticTheorem
    theoremD :
      PCTL.NormalizedQuadraticForcesLorentzSignatureTheorem
    theoremE :
      PCTL.LorentzSignatureForcesCliffordTheorem
    theoremF :
      PCTL.WaveLiftFactorsThroughEvenCliffordTheorem
    theoremG :
      PCTL.ClosureCoreWitnessForcesFullClosureTheorem

canonicalPhysicsClosureTheoremChecklist :
  PhysicsClosureTheoremChecklist
canonicalPhysicsClosureTheoremChecklist =
  record
    { projectionDefectSplitForcesParallelogram =
        λ {m} → PDSP.projectionDefectParallelogramFromSplit {m}
    ; parallelogramForcesQuadratic =
        CFQT.canonicalRealStackContractionForcesQuadraticTheorem
    ; strongContractionNormalizesQuadratic =
        CFQS.canonicalNontrivialInvariantStrong
    ; normalizedQuadraticForcesLorentzSignature =
        CQSB.canonicalContractionQuadraticToSignatureBridgeTheorem
    ; lorentzSignatureForcesClifford =
        QTCB.canonicalQuadraticToCliffordBridgeTheorem
    ; lorentzSignatureForcesSpinDirac =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; waveLiftFactorsThroughEvenClifford =
        CEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    ; closureCoreWitnessForcesFullClosure =
        PCCT.canonicalPhysicsClosureConstructorTheorem
    ; canonicalCoreWitness = PCFI.physicsClosureCoreWitness
    ; canonicalFullClosure = PCFI.physicsClosureFull
    }

canonicalPhysicsClosureHeadlineTheorem :
  PhysicsClosureHeadlineTheorem
canonicalPhysicsClosureHeadlineTheorem =
  record
    { canonicalChecklist = canonicalPhysicsClosureTheoremChecklist
    ; shiftWitness = PCFI.physicsClosureCoreWitness
    ; shiftConstructorTheorem =
        PCCT.canonicalPhysicsClosureConstructorTheorem
    }

canonicalPhysicsClosureNamedTheoremChecklist :
  PhysicsClosureNamedTheoremChecklist
canonicalPhysicsClosureNamedTheoremChecklist =
  record
    { theoremA = PCTL.projectionDefectSplitForcesParallelogramTheorem
    ; theoremB = PCTL.parallelogramForcesQuadraticFormTheorem
    ; theoremC = PCTL.strongContractionNormalizesQuadraticTheorem
    ; theoremD = PCTL.normalizedQuadraticForcesLorentzSignatureTheorem
    ; theoremE = PCTL.lorentzSignatureForcesCliffordTheorem
    ; theoremF = PCTL.waveLiftFactorsThroughEvenCliffordTheorem
    ; theoremG = PCTL.closureCoreWitnessForcesFullClosureTheorem
    }

syntheticPhysicsClosureRealizationIndependenceChecklist :
  PhysicsClosureRealizationIndependenceChecklist
syntheticPhysicsClosureRealizationIndependenceChecklist =
  record
    { canonicalHeadline = canonicalPhysicsClosureHeadlineTheorem
    ; independenceTheorem =
        PCRIT.syntheticPhysicsClosureRealizationIndependenceTheorem
    }
