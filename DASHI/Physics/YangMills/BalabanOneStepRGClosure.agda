module DASHI.Physics.YangMills.BalabanOneStepRGClosure where

------------------------------------------------------------------------
-- Complete one-step RG proof surface.  Every analytic ingredient is explicit;
-- the assembly theorem itself is checked and does not manufacture any bound.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record OneStepRGInputs
    (Field EffectiveAction Polymer Bound : Set) : Set₁ where
  field
    backgroundField : Field → Field
    fluctuationCoordinate : Field → Field → Field
    effectiveAction : Field → EffectiveAction
    irrelevantRemainder : Field → Polymer
    polymerNorm : Polymer → Bound
    outputBound : Bound

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

    LessEqual : Bound → Bound → Set
    irrelevantRemainderBound : ∀ field →
      LessEqual (polymerNorm (irrelevantRemainder field)) outputBound

open OneStepRGInputs public

record OneStepRGCertificate
    (Field EffectiveAction Polymer Bound : Set) : Set₁ where
  field
    inputs : OneStepRGInputs Field EffectiveAction Polymer Bound
    outputAction : Field → EffectiveAction
    outputPolymer : Field → Polymer
    outputActionIsEffectiveAction : ∀ field →
      outputAction field ≡ effectiveAction inputs field
    outputPolymerIsRemainder : ∀ field →
      outputPolymer field ≡ irrelevantRemainder inputs field
    outputPolymerBounded : ∀ field →
      LessEqual inputs
        (polymerNorm inputs (outputPolymer field))
        (outputBound inputs)

open OneStepRGCertificate public

assembleOneStepRG :
  ∀ {Field EffectiveAction Polymer Bound : Set} →
  (inputs : OneStepRGInputs Field EffectiveAction Polymer Bound) →
  OneStepRGCertificate Field EffectiveAction Polymer Bound
assembleOneStepRG inputs = record
  { inputs = inputs
  ; outputAction = effectiveAction inputs
  ; outputPolymer = irrelevantRemainder inputs
  ; outputActionIsEffectiveAction = λ _ → refl
  ; outputPolymerIsRemainder = λ _ → refl
  ; outputPolymerBounded = irrelevantRemainderBound inputs
  }

oneStepRGAssemblyLevel : ProofLevel
oneStepRGAssemblyLevel = machineChecked

oneStepRGAnalyticInputsLevel : ProofLevel
oneStepRGAnalyticInputsLevel = conditional
