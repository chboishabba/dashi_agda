module DASHI.Algebra.Quantum.TreeHeisenbergScalingLimit where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Unified.GRQuantumProofTerms as Legacy

------------------------------------------------------------------------
-- Hilbert completion and tree-to-Heisenberg scaling limit.
--
-- Finite qutrit Weyl relations do not by themselves provide an unbounded
-- self-adjoint canonical pair.  The authority below separates completion,
-- dense-domain control, finite-tree approximants, operator convergence, and the
-- limiting CCR on a common invariant core.

record PreHilbertCompletion : Set₁ where
  field
    Scalar : Set
    PreHilbertState : Set
    HilbertState : Set

    zero : HilbertState
    add : HilbertState → HilbertState → HilbertState
    scale : Scalar → HilbertState → HilbertState
    inner : HilbertState → HilbertState → Scalar

    embed : PreHilbertState → HilbertState
    CauchySequence : Set
    cauchyTerm : CauchySequence → Nat → PreHilbertState
    completionLimit : CauchySequence → HilbertState

    preInnerProductLaws : Set
    preInnerProductLawsProof : preInnerProductLaws
    positiveDefiniteAfterNullQuotient : Set
    positiveDefiniteAfterNullQuotientProof :
      positiveDefiniteAfterNullQuotient
    embeddingIsometric : Set
    embeddingIsometricProof : embeddingIsometric
    embeddingDense : Set
    embeddingDenseProof : embeddingDense
    hilbertComplete : Set
    hilbertCompleteProof : hilbertComplete
open PreHilbertCompletion public

record TreeOperatorScalingFamily
  (completion : PreHilbertCompletion) : Set₁ where
  field
    Resolution : Set
    TreeState : Resolution → Set
    treeEmbed :
      (resolution : Resolution) →
      TreeState resolution → HilbertState completion

    TreeOperator : Resolution → Set
    configurationAt :
      (resolution : Resolution) → TreeOperator resolution
    momentumAt :
      (resolution : Resolution) → TreeOperator resolution
    identityAt :
      (resolution : Resolution) → TreeOperator resolution
    commutatorAt :
      (resolution : Resolution) →
      TreeOperator resolution → TreeOperator resolution →
      TreeOperator resolution

    ContinuumOperator : Set
    configurationLimit : ContinuumOperator
    momentumLimit : ContinuumOperator
    identityLimit : ContinuumOperator
    commutatorLimit :
      ContinuumOperator → ContinuumOperator → ContinuumOperator

    CommonInvariantCore : Set
    coreEmbed : CommonInvariantCore → HilbertState completion
    applyContinuum :
      ContinuumOperator → CommonInvariantCore → HilbertState completion

    finiteTreeWeylLaw : Set
    finiteTreeWeylLawProof : finiteTreeWeylLaw
    scalingParametersDeclared : Set
    scalingParametersDeclaredProof : scalingParametersDeclared
    configurationConvergesOnCore : Set
    configurationConvergesOnCoreProof : configurationConvergesOnCore
    momentumConvergesOnCore : Set
    momentumConvergesOnCoreProof : momentumConvergesOnCore
    commutatorsConvergeOnCore : Set
    commutatorsConvergeOnCoreProof : commutatorsConvergeOnCore
    limitingCCR : Set
    limitingCCRProof : limitingCCR
    essentialSelfAdjointnessOrClosedExtensions : Set
    essentialSelfAdjointnessOrClosedExtensionsProof :
      essentialSelfAdjointnessOrClosedExtensions
    exponentialsGiveStronglyContinuousUnitaryGroups : Set
    exponentialsGiveStronglyContinuousUnitaryGroupsProof :
      exponentialsGiveStronglyContinuousUnitaryGroups
open TreeOperatorScalingFamily public

record HilbertTreeHeisenbergAuthority : Set₁ where
  field
    completion : PreHilbertCompletion
    scalingFamily : TreeOperatorScalingFamily completion

    bornMeasureExtendsContinuously : Set
    bornMeasureExtendsContinuouslyProof : bornMeasureExtendsContinuously
    orthogonalProbabilityAdditivityOnCompletion : Set
    orthogonalProbabilityAdditivityOnCompletionProof :
      orthogonalProbabilityAdditivityOnCompletion
    finiteRepresentationsDoNotImplyUnboundedCCRAlone : Set
    finiteRepresentationsDoNotImplyUnboundedCCRAloneProof :
      finiteRepresentationsDoNotImplyUnboundedCCRAlone

    legacySurface : Legacy.WaveLiftCCRProof
    legacyClosed : Legacy.WaveLiftCCRClosed legacySurface
    legacyCylinderEmbeddingAgrees : Set
    legacyCylinderEmbeddingAgreesProof : legacyCylinderEmbeddingAgrees
    legacyCCRIsTheScalingLimitCCR : Set
    legacyCCRIsTheScalingLimitCCRProof : legacyCCRIsTheScalingLimitCCR
open HilbertTreeHeisenbergAuthority public

heisenbergLegacySurface :
  HilbertTreeHeisenbergAuthority → Legacy.WaveLiftCCRProof
heisenbergLegacySurface = legacySurface

heisenbergLegacyClosed :
  (authority : HilbertTreeHeisenbergAuthority) →
  Legacy.WaveLiftCCRClosed (heisenbergLegacySurface authority)
heisenbergLegacyClosed = legacyClosed
