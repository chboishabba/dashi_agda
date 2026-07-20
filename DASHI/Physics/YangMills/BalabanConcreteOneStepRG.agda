module DASHI.Physics.YangMills.BalabanConcreteOneStepRG where

------------------------------------------------------------------------
-- Concrete one-step RG assembly from the explicit polymer budget theorem.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOneStepPolymerEstimate as Polymer
import DASHI.Physics.YangMills.BalabanOneStepRGClosure as RG

record OneStepRGStructure
    (Field EffectiveAction : Set) : Set₁ where
  field
    backgroundField : Field → Field
    fluctuationCoordinate : Field → Field → Field
    effectiveAction : Field → EffectiveAction

    FluctuationParametrizationValid : Set
    JacobianControlled : Set
    DeterminantControlled : Set
    BCHRemainderControlled : Set
    WardIdentityPreserved : Set
    EffectiveActionLocalized : Set
    VacuumEnergyRenormalized : Set
    CouplingRenormalized : Set

    fluctuationParametrizationValid : FluctuationParametrizationValid
    jacobianControlled : JacobianControlled
    determinantControlled : DeterminantControlled
    bchRemainderControlled : BCHRemainderControlled
    wardIdentityPreserved : WardIdentityPreserved
    effectiveActionLocalized : EffectiveActionLocalized
    vacuumEnergyRenormalized : VacuumEnergyRenormalized
    couplingRenormalized : CouplingRenormalized

open OneStepRGStructure public

toOneStepRGInputs :
  ∀ {Field EffectiveAction PolymerCarrier Bound : Set} →
  OneStepRGStructure Field EffectiveAction →
  Polymer.OneStepPolymerEstimateData Field PolymerCarrier Bound →
  RG.OneStepRGInputs Field EffectiveAction PolymerCarrier Bound
toOneStepRGInputs structure estimate = record
  { backgroundField = backgroundField structure
  ; fluctuationCoordinate = fluctuationCoordinate structure
  ; effectiveAction = effectiveAction structure
  ; irrelevantRemainder = Polymer.outputPolymer estimate
  ; polymerNorm = Polymer.polymerNorm estimate
  ; outputBound = Polymer.oneStepPolymerBudget estimate
  ; FluctuationParametrizationValid = FluctuationParametrizationValid structure
  ; JacobianControlled = JacobianControlled structure
  ; DeterminantControlled = DeterminantControlled structure
  ; BCHRemainderControlled = BCHRemainderControlled structure
  ; WardIdentityPreserved = WardIdentityPreserved structure
  ; EffectiveActionLocalized = EffectiveActionLocalized structure
  ; VacuumEnergyRenormalized = VacuumEnergyRenormalized structure
  ; CouplingRenormalized = CouplingRenormalized structure
  ; fluctuationParametrizationValid = fluctuationParametrizationValid structure
  ; jacobianControlled = jacobianControlled structure
  ; determinantControlled = determinantControlled structure
  ; bchRemainderControlled = bchRemainderControlled structure
  ; wardIdentityPreserved = wardIdentityPreserved structure
  ; effectiveActionLocalized = effectiveActionLocalized structure
  ; vacuumEnergyRenormalized = vacuumEnergyRenormalized structure
  ; couplingRenormalized = couplingRenormalized structure
  ; LessEqual = Polymer.LessEqual (Polymer.order estimate)
  ; irrelevantRemainderBound = Polymer.oneStepPolymerEstimate estimate
  }

concreteOneStepRGCertificate :
  ∀ {Field EffectiveAction PolymerCarrier Bound : Set} →
  OneStepRGStructure Field EffectiveAction →
  Polymer.OneStepPolymerEstimateData Field PolymerCarrier Bound →
  RG.OneStepRGCertificate Field EffectiveAction PolymerCarrier Bound
concreteOneStepRGCertificate structure estimate =
  RG.assembleOneStepRG (toOneStepRGInputs structure estimate)

concreteOneStepRGAssemblyLevel : ProofLevel
concreteOneStepRGAssemblyLevel = machineChecked

concreteOneStepRGAnalyticStructureLevel : ProofLevel
concreteOneStepRGAnalyticStructureLevel = conditional
