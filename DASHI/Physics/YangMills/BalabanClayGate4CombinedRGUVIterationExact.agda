module DASHI.Physics.YangMills.BalabanClayGate4CombinedRGUVIterationExact where

open import Agda.Builtin.Nat using (Nat; suc)
import Agda.Builtin.Nat as Nat

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Target locator pending direct primary-source verification:
-- Theorem 1, p. 388, for preservation of the inductive parameters and the
-- complete small-/large-field renormalization step.
--
-- Relationship: the one-step analytic inequalities remain external inputs.
-- Their packaging into one admissible RG state and the all-scale induction are
-- exact constructions proved in this module.
------------------------------------------------------------------------

record CombinedOneStepPolymerNormData
    (State Bound : Set) : Set₁ where
  field
    next : State → State
    norm : State → Bound

    zero one lambda : Bound
    perturbativeError : State → Bound
    add multiply : Bound → Bound → Bound
    LessEqual StrictLess : Bound → Bound → Set

    combinedOneStepPolymerNorm : ∀ (state : State) →
      LessEqual
        (norm (next state))
        (add
          (multiply lambda (norm state))
          (perturbativeError state))

    combinedContractionStrict : StrictLess lambda one

open CombinedOneStepPolymerNormData public

record CombinedRGAdmissibility
    {State Bound : Set}
    (normData : CombinedOneStepPolymerNormData State Bound) : Set₁ where
  field
    AdmissibleCoupling : State → Set
    BoundaryAdmissible : State → Set
    PolymerNormAdmissible : State → Set

    admissibleCouplingDomainPreserved : ∀ (state : State) →
      AdmissibleCoupling state →
      AdmissibleCoupling (next normData state)

    boundaryTermsRemainAdmissible : ∀ (state : State) →
      BoundaryAdmissible state →
      BoundaryAdmissible (next normData state)

    combinedPolymerNormCloses : ∀ (state : State) →
      PolymerNormAdmissible state →
      PolymerNormAdmissible (next normData state)

open CombinedRGAdmissibility public

record AdmissibleRGState
    {State Bound : Set}
    {normData : CombinedOneStepPolymerNormData State Bound}
    (admissibility : CombinedRGAdmissibility normData)
    (state : State) : Set where
  field
    couplingAdmissible : AdmissibleCoupling admissibility state
    boundaryAdmissible : BoundaryAdmissible admissibility state
    polymerNormAdmissible : PolymerNormAdmissible admissibility state

open AdmissibleRGState public

combinedStepPreservesAdmissibility :
  ∀ {State Bound}
    {normData : CombinedOneStepPolymerNormData State Bound}
    (admissibility : CombinedRGAdmissibility normData)
    (state : State) →
  AdmissibleRGState admissibility state →
  AdmissibleRGState admissibility (next normData state)
combinedStepPreservesAdmissibility admissibility state evidence = record
  { couplingAdmissible =
      admissibleCouplingDomainPreserved admissibility state
        (couplingAdmissible evidence)
  ; boundaryAdmissible =
      boundaryTermsRemainAdmissible admissibility state
        (boundaryAdmissible evidence)
  ; polymerNormAdmissible =
      combinedPolymerNormCloses admissibility state
        (polymerNormAdmissible evidence)
  }

stateAt :
  ∀ {State Bound} →
  CombinedOneStepPolymerNormData State Bound → State → Nat → State
stateAt normData initial Nat.zero = initial
stateAt normData initial (suc scale) =
  next normData (stateAt normData initial scale)

allScaleAdmissible :
  ∀ {State Bound}
    (normData : CombinedOneStepPolymerNormData State Bound)
    (admissibility : CombinedRGAdmissibility normData)
    (initial : State) →
  AdmissibleRGState admissibility initial →
  ∀ (scale : Nat) →
  AdmissibleRGState admissibility (stateAt normData initial scale)
allScaleAdmissible normData admissibility initial initialEvidence Nat.zero =
  initialEvidence
allScaleAdmissible normData admissibility initial initialEvidence (suc scale) =
  combinedStepPreservesAdmissibility admissibility
    (stateAt normData initial scale)
    (allScaleAdmissible normData admissibility initial initialEvidence scale)

------------------------------------------------------------------------
-- Uniform effective-density and partition-function consequences.
------------------------------------------------------------------------

record UniformUVConsequences
    {State Bound : Set}
    (normData : CombinedOneStepPolymerNormData State Bound) : Set₁ where
  field
    UniformlyStable : State → Set
    PartitionFunctionUniformlyBounded : State → Set

    stabilityPreserved : ∀ (state : State) →
      UniformlyStable state → UniformlyStable (next normData state)

    partitionBoundFromStable : ∀ (state : State) →
      UniformlyStable state → PartitionFunctionUniformlyBounded state

open UniformUVConsequences public

record InitialUVStability
    {State Bound : Set}
    {normData : CombinedOneStepPolymerNormData State Bound}
    (consequences : UniformUVConsequences normData)
    (initial : State) : Set where
  field
    initialUniformlyStable : UniformlyStable consequences initial

open InitialUVStability public

allScaleUniformlyStable :
  ∀ {State Bound}
    (normData : CombinedOneStepPolymerNormData State Bound)
    (consequences : UniformUVConsequences normData)
    (initial : State) →
  InitialUVStability consequences initial →
  ∀ (scale : Nat) → UniformlyStable consequences (stateAt normData initial scale)
allScaleUniformlyStable normData consequences initial initialData Nat.zero =
  initialUniformlyStable initialData
allScaleUniformlyStable normData consequences initial initialData (suc scale) =
  stabilityPreserved consequences
    (stateAt normData initial scale)
    (allScaleUniformlyStable normData consequences initial initialData scale)

partitionFunctionUniformBound :
  ∀ {State Bound}
    (normData : CombinedOneStepPolymerNormData State Bound)
    (consequences : UniformUVConsequences normData)
    (initial : State) →
  InitialUVStability consequences initial →
  ∀ (scale : Nat) →
  PartitionFunctionUniformlyBounded consequences
    (stateAt normData initial scale)
partitionFunctionUniformBound normData consequences initial initialData scale =
  partitionBoundFromStable consequences
    (stateAt normData initial scale)
    (allScaleUniformlyStable normData consequences initial initialData scale)

record Gate4UVCompletionPackage
    (State Bound : Set) : Set₁ where
  field
    normData : CombinedOneStepPolymerNormData State Bound
    admissibility : CombinedRGAdmissibility normData
    consequences : UniformUVConsequences normData
    initial : State
    initialAdmissible : AdmissibleRGState admissibility initial
    initialStable : InitialUVStability consequences initial

open Gate4UVCompletionPackage public

packageAllScaleAdmissible :
  ∀ {State Bound}
    (package : Gate4UVCompletionPackage State Bound)
    (scale : Nat) →
  AdmissibleRGState (admissibility package)
    (stateAt (normData package) (initial package) scale)
packageAllScaleAdmissible package =
  allScaleAdmissible
    (normData package)
    (admissibility package)
    (initial package)
    (initialAdmissible package)

packagePartitionFunctionUniformBound :
  ∀ {State Bound}
    (package : Gate4UVCompletionPackage State Bound)
    (scale : Nat) →
  PartitionFunctionUniformlyBounded (consequences package)
    (stateAt (normData package) (initial package) scale)
packagePartitionFunctionUniformBound package =
  partitionFunctionUniformBound
    (normData package)
    (consequences package)
    (initial package)
    (initialStable package)

combinedAdmissibilityAssemblyLevel : ProofLevel
combinedAdmissibilityAssemblyLevel = machineChecked

allScaleAdmissibilityInductionLevel : ProofLevel
allScaleAdmissibilityInductionLevel = machineChecked

allScaleUniformStabilityInductionLevel : ProofLevel
allScaleUniformStabilityInductionLevel = machineChecked

partitionFunctionUniformBoundAssemblyLevel : ProofLevel
partitionFunctionUniformBoundAssemblyLevel = machineChecked

combinedOneStepAnalyticInputsLevel : ProofLevel
combinedOneStepAnalyticInputsLevel = conditional

initialUVStabilityInputsLevel : ProofLevel
initialUVStabilityInputsLevel = conditional
