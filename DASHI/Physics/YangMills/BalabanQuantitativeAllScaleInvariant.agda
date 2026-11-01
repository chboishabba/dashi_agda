module DASHI.Physics.YangMills.BalabanQuantitativeAllScaleInvariant where

------------------------------------------------------------------------
-- Quantitative all-scale invariant domain.
--
-- Instead of assuming one opaque admissibility predicate, the domain is split
-- into the running-coupling, field-radius, polymer, analyticity, gauge-fixing,
-- and locality obligations needed by the next RG step.  Componentwise one-step
-- preservation is assembled into the exact induction used at all scales.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanAllScaleRGClosure as RG

record RGAdmissibilityProfile (State : Set) : Set₁ where
  field
    CouplingAdmissible : Nat → State → Set
    FieldRadiusAdmissible : Nat → State → Set
    PolymerAdmissible : Nat → State → Set
    AnalyticityAdmissible : Nat → State → Set
    GaugeFixingAdmissible : Nat → State → Set
    LocalityAdmissible : Nat → State → Set

open RGAdmissibilityProfile public

record AdmissibleAt
    {State : Set}
    (profile : RGAdmissibilityProfile State)
    (scale : Nat)
    (state : State) : Set where
  field
    coupling : CouplingAdmissible profile scale state
    fieldRadius : FieldRadiusAdmissible profile scale state
    polymer : PolymerAdmissible profile scale state
    analyticity : AnalyticityAdmissible profile scale state
    gaugeFixing : GaugeFixingAdmissible profile scale state
    locality : LocalityAdmissible profile scale state

open AdmissibleAt public

record QuantitativeRGStep (State : Set) : Set₁ where
  field
    profile : RGAdmissibilityProfile State
    renormalize : Nat → State → State

    couplingPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      CouplingAdmissible profile (suc scale) (renormalize scale state)
    fieldRadiusPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      FieldRadiusAdmissible profile (suc scale) (renormalize scale state)
    polymerPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      PolymerAdmissible profile (suc scale) (renormalize scale state)
    analyticityPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      AnalyticityAdmissible profile (suc scale) (renormalize scale state)
    gaugeFixingPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      GaugeFixingAdmissible profile (suc scale) (renormalize scale state)
    localityPreserved : ∀ scale state →
      AdmissibleAt profile scale state →
      LocalityAdmissible profile (suc scale) (renormalize scale state)

open QuantitativeRGStep public

stepPreservesAdmissible :
  ∀ {State : Set} →
  (stepData : QuantitativeRGStep State) →
  ∀ scale state →
  AdmissibleAt (profile stepData) scale state →
  AdmissibleAt (profile stepData) (suc scale)
    (renormalize stepData scale state)
stepPreservesAdmissible stepData scale state admissible = record
  { coupling = couplingPreserved stepData scale state admissible
  ; fieldRadius = fieldRadiusPreserved stepData scale state admissible
  ; polymer = polymerPreserved stepData scale state admissible
  ; analyticity = analyticityPreserved stepData scale state admissible
  ; gaugeFixing = gaugeFixingPreserved stepData scale state admissible
  ; locality = localityPreserved stepData scale state admissible
  }

record QuantitativeAllScaleInputs
    (State ErrorBound : Set) : Set₁ where
  field
    stepData : QuantitativeRGStep State
    initialState : State
    initialAdmissible : AdmissibleAt (profile stepData) zero initialState
    errors : RG.SummableRGErrors ErrorBound

open QuantitativeAllScaleInputs public

toRGInvariantDomain :
  ∀ {State ErrorBound : Set} →
  QuantitativeAllScaleInputs State ErrorBound →
  RG.RGInvariantDomain State
toRGInvariantDomain inputs = record
  { renormalize = renormalize (stepData inputs)
  ; Admissible = AdmissibleAt (profile (stepData inputs))
  ; initialState = initialState inputs
  ; initialAdmissible = initialAdmissible inputs
  ; oneStepPreserves = stepPreservesAdmissible (stepData inputs)
  }

quantitativeAllScaleCertificate :
  ∀ {State ErrorBound : Set} →
  QuantitativeAllScaleInputs State ErrorBound →
  RG.AllScaleRGCertificate State ErrorBound
quantitativeAllScaleCertificate inputs =
  RG.assembleAllScaleRG (toRGInvariantDomain inputs) (errors inputs)

quantitativeInvariantAssemblyLevel : ProofLevel
quantitativeInvariantAssemblyLevel = machineChecked

quantitativeOneStepPreservationInputsLevel : ProofLevel
quantitativeOneStepPreservationInputsLevel = conjectural
