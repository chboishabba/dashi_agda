module DASHI.Physics.YangMills.BalabanExplicitAllScaleInvariant where

------------------------------------------------------------------------
-- Explicit I1--I9 invariant-domain closure.
--
-- Admissibility is decomposed into its six requested components.  One-step
-- preservation is assembled componentwise, initial admissibility is explicit,
-- error summability exposes its total witness, and the all-scale conclusion is
-- obtained by exact induction.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record AllScaleInvariantData (State ErrorBound : Set) : Set₁ where
  field
    state : Nat → State
    nextState : Nat → State → State
    stateStep : ∀ scale → state (suc scale) ≡ nextState scale (state scale)

    CouplingAdmissible FieldRadiusAdmissible PolymerAdmissible :
      Nat → State → Set
    AnalyticityAdmissible GaugeFixingAdmissible LocalityAdmissible :
      Nat → State → Set

    couplingInitial : CouplingAdmissible zero (state zero)
    fieldRadiusInitial : FieldRadiusAdmissible zero (state zero)
    polymerInitial : PolymerAdmissible zero (state zero)
    analyticityInitial : AnalyticityAdmissible zero (state zero)
    gaugeFixingInitial : GaugeFixingAdmissible zero (state zero)
    localityInitial : LocalityAdmissible zero (state zero)

    couplingStep : ∀ scale current →
      CouplingAdmissible scale current →
      CouplingAdmissible (suc scale) (nextState scale current)
    fieldRadiusStep : ∀ scale current →
      FieldRadiusAdmissible scale current →
      FieldRadiusAdmissible (suc scale) (nextState scale current)
    polymerStep : ∀ scale current →
      PolymerAdmissible scale current →
      PolymerAdmissible (suc scale) (nextState scale current)
    analyticityStep : ∀ scale current →
      AnalyticityAdmissible scale current →
      AnalyticityAdmissible (suc scale) (nextState scale current)
    gaugeFixingStep : ∀ scale current →
      GaugeFixingAdmissible scale current →
      GaugeFixingAdmissible (suc scale) (nextState scale current)
    localityStep : ∀ scale current →
      LocalityAdmissible scale current →
      LocalityAdmissible (suc scale) (nextState scale current)

    partialErrorSum : Nat → ErrorBound
    LessEqual : ErrorBound → ErrorBound → Set
    totalError : ErrorBound
    partialErrorBound : ∀ scale → LessEqual (partialErrorSum scale) totalError

open AllScaleInvariantData public

record AdmissibleAt
    {State ErrorBound : Set}
    (dataSet : AllScaleInvariantData State ErrorBound)
    (scale : Nat) (current : State) : Set where
  constructor admissible
  field
    coupling : CouplingAdmissible dataSet scale current
    fieldRadius : FieldRadiusAdmissible dataSet scale current
    polymer : PolymerAdmissible dataSet scale current
    analyticity : AnalyticityAdmissible dataSet scale current
    gaugeFixing : GaugeFixingAdmissible dataSet scale current
    locality : LocalityAdmissible dataSet scale current

open AdmissibleAt public

couplingPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → CouplingAdmissible dataSet scale current →
  CouplingAdmissible dataSet (suc scale) (nextState dataSet scale current)
couplingPreserved = couplingStep

fieldRadiusPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → FieldRadiusAdmissible dataSet scale current →
  FieldRadiusAdmissible dataSet (suc scale) (nextState dataSet scale current)
fieldRadiusPreserved = fieldRadiusStep

polymerPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → PolymerAdmissible dataSet scale current →
  PolymerAdmissible dataSet (suc scale) (nextState dataSet scale current)
polymerPreserved = polymerStep

analyticityPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → AnalyticityAdmissible dataSet scale current →
  AnalyticityAdmissible dataSet (suc scale) (nextState dataSet scale current)
analyticityPreserved = analyticityStep

gaugeFixingPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → GaugeFixingAdmissible dataSet scale current →
  GaugeFixingAdmissible dataSet (suc scale) (nextState dataSet scale current)
gaugeFixingPreserved = gaugeFixingStep

localityPreserved :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → LocalityAdmissible dataSet scale current →
  LocalityAdmissible dataSet (suc scale) (nextState dataSet scale current)
localityPreserved = localityStep

initialScaleAdmissible :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  AdmissibleAt dataSet zero (state dataSet zero)
initialScaleAdmissible dataSet = admissible
  (couplingInitial dataSet)
  (fieldRadiusInitial dataSet)
  (polymerInitial dataSet)
  (analyticityInitial dataSet)
  (gaugeFixingInitial dataSet)
  (localityInitial dataSet)

oneStepAdmissible :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale current → AdmissibleAt dataSet scale current →
  AdmissibleAt dataSet (suc scale) (nextState dataSet scale current)
oneStepAdmissible dataSet scale current hypothesis = admissible
  (couplingPreserved dataSet scale current (coupling hypothesis))
  (fieldRadiusPreserved dataSet scale current (fieldRadius hypothesis))
  (polymerPreserved dataSet scale current (polymer hypothesis))
  (analyticityPreserved dataSet scale current (analyticity hypothesis))
  (gaugeFixingPreserved dataSet scale current (gaugeFixing hypothesis))
  (localityPreserved dataSet scale current (locality hypothesis))

rgErrorsSummable :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  Σ ErrorBound (λ total →
    ∀ scale → LessEqual dataSet (partialErrorSum dataSet scale) total)
rgErrorsSummable dataSet = totalError dataSet , partialErrorBound dataSet

allScaleRGAdmissible :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ∀ scale → AdmissibleAt dataSet scale (state dataSet scale)
allScaleRGAdmissible dataSet zero = initialScaleAdmissible dataSet
allScaleRGAdmissible dataSet (suc scale) rewrite stateStep dataSet scale =
  oneStepAdmissible dataSet scale (state dataSet scale)
    (allScaleRGAdmissible dataSet scale)

record ExplicitAllScaleCertificate (State ErrorBound : Set) : Set₁ where
  field
    dataSet : AllScaleInvariantData State ErrorBound
    initial : AdmissibleAt dataSet zero (state dataSet zero)
    errorsSummable : Σ ErrorBound (λ total →
      ∀ scale → LessEqual dataSet (partialErrorSum dataSet scale) total)
    admissibleAtEveryScale : ∀ scale →
      AdmissibleAt dataSet scale (state dataSet scale)

open ExplicitAllScaleCertificate public

assembleExplicitAllScale :
  ∀ {State ErrorBound : Set} →
  (dataSet : AllScaleInvariantData State ErrorBound) →
  ExplicitAllScaleCertificate State ErrorBound
assembleExplicitAllScale dataSet = record
  { dataSet = dataSet
  ; initial = initialScaleAdmissible dataSet
  ; errorsSummable = rgErrorsSummable dataSet
  ; admissibleAtEveryScale = allScaleRGAdmissible dataSet
  }

explicitAllScaleInductionLevel : ProofLevel
explicitAllScaleInductionLevel = machineChecked

explicitAllScaleComponentInputsLevel : ProofLevel
explicitAllScaleComponentInputsLevel = conditional
