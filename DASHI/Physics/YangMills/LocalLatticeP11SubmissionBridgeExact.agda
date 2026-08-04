module DASHI.Physics.YangMills.LocalLatticeP11SubmissionBridgeExact where

------------------------------------------------------------------------
-- Exact non-postulated P11 handoff.
--
-- LocalLatticeDischargePipeline currently offers a compatibility constructor
-- whose source-input record uses postulatedAbsorptionConditionWitness.  This
-- module adds the submission path: a caller supplies either an explicit
-- ImportedAbsorptionCondition or the reduced uniform-minimum inputs from
-- BalabanP11UniformAbsorptionReductionExact.  All remaining local-lattice
-- fields are reused unchanged.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (refl)

import DASHI.Physics.YangMills.LocalLatticeDischargePipeline as Local
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as Anisotropic
import DASHI.Physics.YangMills.BalabanP11UniformAbsorptionReductionExact as P11
open import DASHI.Physics.YangMills.CompactLieProofLevel

localLatticeStepVSourceInputsWithP11 :
  Local.LocalLatticeAnalyticDischargePackage →
  LargeField.ImportedAbsorptionCondition →
  Assembly.StepVSourceAnalyticInputs
localLatticeStepVSourceInputsWithP11 package p11 = record
  { p06AnimalCounting =
      Local.LocalLatticeP06CountingWitness package
  ; p06MixedReducerPayload =
      Local.LocalLatticeAnalyticDischargePackage.p06MixedReducerPayload package
  ; p06MixedReducerPayloadMatches = refl
  ; p10LargeFieldActivity =
      LargeField.P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  ; p11AbsorptionCondition = p11
  ; p33aUniformLinkEllipticity =
      Anisotropic.P33DiameterLaneFromAnalyticDischarge.p33aWrapper
        (Local.LocalLatticeP33DiameterLane package)
  }

localLatticeStepVFromExplicitP11 :
  (package : Local.LocalLatticeAnalyticDischargePackage) →
  LargeField.ImportedAbsorptionCondition →
  Assembly.StepVSpatialKPCertificate
localLatticeStepVFromExplicitP11 package p11 =
  Assembly.StepVFromDischargePackages
    (localLatticeStepVSourceInputsWithP11 package p11)
    (Local.LocalLatticeStepVInternalReducers package)

localLatticeStepVFromUniformP0Minimum :
  (package : Local.LocalLatticeAnalyticDischargePackage) →
  P11.P11UniformAbsorptionInputs →
  Assembly.StepVSpatialKPCertificate
localLatticeStepVFromUniformP0Minimum package inputs =
  localLatticeStepVFromExplicitP11
    package
    (P11.p11AbsorptionConditionFromUniformMinimum inputs)

localLatticeExplicitP11BridgeLevel : ProofLevel
localLatticeExplicitP11BridgeLevel = machineChecked

localLatticeUniformP0InputsLevel : ProofLevel
localLatticeUniformP0InputsLevel = conditional
