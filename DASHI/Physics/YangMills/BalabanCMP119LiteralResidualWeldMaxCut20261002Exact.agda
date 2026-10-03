{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP119LiteralResidualWeldMaxCut20261002Exact where

------------------------------------------------------------------------
-- CMP119 LITERAL RESIDUAL-WELD MAX-CUT
--
-- This module composes the strongest existing source-shaped donors without
-- inventing another residual representation.
--
-- Existing source objects:
--   * Eq. (2.23): one effective action assembled from Wilson/E/R/B/vacuum;
--   * E_k: localized composite sum on the selected Section-2 density;
--   * R_k: CMP122 Eq. (1.100) rooted-shell envelope, with exact dyadic shell
--          transfer after the existing weight-split/entropy inputs;
--   * B_k: source-native boundary object, with analytic/localized reinjection;
--   * vacuum: one scale-indexed source object, canonically constant on the
--             configuration carrier;
--   * B/R source polymers: executable positive/negative/crossing OS support
--     classification once their published Polymer carrier is identified with
--     the literal periodic block-polymer carrier.
--
-- The remaining literal Lean weld is therefore NOT another dyadic theorem.
-- It is the common-evaluator theorem saying that evaluation of the selected
-- Eq. (2.23) action is the Wilson action plus the evaluated E/R/B/vacuum
-- sectors on the same configuration, together with the identification of the
-- E/R/B localized pieces with the shellContribution family consumed by Lean.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw
import DASHI.Physics.YangMills.BalabanCMP119RegularESection2PredicateRound246Exact as E
import DASHI.Physics.YangMills.BalabanCMP122Equation1100EntropyBudgetExact as R
import DASHI.Physics.YangMills.BalabanCMP119ReflectionMaxCut20261002Exact as RP
import DASHI.Physics.YangMills.BalabanCMP109116FiniteEffectiveActionHessianRound103Exact as Finite
import DASHI.Physics.YangMills.BalabanYM4ROperationEntropyShellExact as Shell
import DASHI.Physics.YangMills.BalabanYM4LargeFieldContributionSharedSlackExact as LF
import DASHI.Physics.YangMills.BalabanCMP122Equation1100DirectExact as RSource
import DASHI.Physics.YangMills.BalabanCMP119ReflectionPolymerGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP119BoundaryReflectionSupportCutExact as BSupport
import DASHI.Physics.YangMills.BalabanCMP122ROperationReflectionSupportCutExact as RSupport

------------------------------------------------------------------------
-- Eq. (2.23) survives any selected action evaluator on the SAME source action.
------------------------------------------------------------------------

evaluatedEquation223 :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    (evaluateAction : Action → Configuration → ℝ)
    scale configuration →
  evaluateAction (Raw.effectiveAction source scale) configuration
  ≡
  evaluateAction
    (Raw.assemble (Raw.actionAlgebra source)
      (Raw.wilsonCoefficient source scale)
      (Raw.wilsonActionTerm source scale)
      (Raw.regularSmallFieldTerm source scale)
      (Raw.rOperationTerm source scale)
      (Raw.boundaryTerm source scale)
      (Raw.vacuumEnergy source scale))
    configuration
evaluatedEquation223 source evaluateAction scale configuration =
  cong
    (λ action → evaluateAction action configuration)
    (Raw.equation223 source scale)

------------------------------------------------------------------------
-- Existing E donor: literal localized composite sum.
------------------------------------------------------------------------

regularELocalizedCompositeSum :
  ∀ {Density Background Volume Component scale density}
    (form : E.CMP119RegularESection2Form
      Density Background Volume Component scale density)
    volume background →
  E.regularE form background
  ≡
  Finite.sumFunctions
      (Finite.mapList
        (E.localizedRegularActivity form volume)
        (E.components form volume))
      background
regularELocalizedCompositeSum form =
  E.regularEIsLocalizedCompositeSum form

------------------------------------------------------------------------
-- Existing R donor: rooted source shell is already below the dyadic envelope.
------------------------------------------------------------------------

rOperationRootedShellBelowDyadic :
  ∀ {Scale Volume Root Polymer Boundary}
    (dataSet : R.Equation1100RootedEntropyData
      Scale Volume Root Polymer Boundary)
    scale volume root depth →
  Shell.rootedRActivityShell
      (R.cmp122Equation1100RootedShell dataSet)
      scale volume root depth
  ≤
  LF.scaledShellMajorant
      (RSource.p0Suppression
        (R.source dataSet) scale)
      depth
rOperationRootedShellBelowDyadic =
  R.cmp122Equation1100ShellAmplitudeExact

------------------------------------------------------------------------
-- Existing vacuum donor: source coordinate has a canonical constant
-- configuration realization.  The action-evaluator identification is separate.
------------------------------------------------------------------------

vacuumSourceConstant :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) →
  Nat → Configuration → Vacuum
vacuumSourceConstant = RP.sourceVacuumConstant

vacuumSourceConstantIndependent :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum Configuration}
    (source : Raw.CMP119SourceNativeRawState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum)
    scale (left right : Configuration) →
  vacuumSourceConstant source scale left
  ≡ vacuumSourceConstant source scale right
vacuumSourceConstantIndependent =
  RP.sourceVacuumConstantIndependent

------------------------------------------------------------------------
-- Precise surviving source-to-Lean weld leaves.
------------------------------------------------------------------------

data LiteralResidualWeldLeaf : Set where
  commonActionEvaluatorAdditiveSemantics
  regularESelectedCarrierInstantiation
  rOperationWeightSplitAndRootedEntropy
  boundaryLocalizedTermsToSelectedShells
  vacuumEvaluatorIsSourceConstant
  fullResidualEqualsSelectedFiniteShellTail : LiteralResidualWeldLeaf

literalResidualWeldCompilerLevel : ProofLevel
literalResidualWeldCompilerLevel = machineChecked

-- Already theorem-bearing donor levels.
regularELocalizedCompositeDonorLevel : ProofLevel
regularELocalizedCompositeDonorLevel = E.activeRegularESection2PredicateCompilerLevel

rOperationDyadicShellDonorLevel : ProofLevel
rOperationDyadicShellDonorLevel = R.cmp122Equation1100EntropyAssemblyLevel

vacuumConstantCarrierDonorLevel : ProofLevel
vacuumConstantCarrierDonorLevel = RP.cmp119ReflectionMaxCutCompilerLevel

-- The common periodic-polymer OS classifier itself is now executable.
reflectionPolymerGeometryDonorLevel : ProofLevel
reflectionPolymerGeometryDonorLevel = Geometry.reflectionPolymerGeometryCompilerLevel

-- B terms already inherit the OS class of the SAME source polymer once the
-- source Polymer parameter is the periodic block carrier.
boundaryReflectionSupportDonorLevel : ProofLevel
boundaryReflectionSupportDonorLevel = BSupport.boundaryReflectionSupportCutCompilerLevel

-- Eq. (1.100) R terms likewise retain their source norm/decay while being
-- classified by the SAME source polymer.
rOperationReflectionSupportDonorLevel : ProofLevel
rOperationReflectionSupportDonorLevel = RSupport.rOperationReflectionSupportCutCompilerLevel

-- Genuine remaining physical/same-object leaves.
commonActionEvaluatorAdditiveSemanticsLevel : ProofLevel
commonActionEvaluatorAdditiveSemanticsLevel = conditional

regularESelectedCarrierInstantiationLevel : ProofLevel
regularESelectedCarrierInstantiationLevel =
  E.literalCMP119RegularESection2PredicateInstantiationLevel

-- R's dyadic arithmetic is already downstream; the surviving source payment is
-- the published-polymer dictionary plus the existing weight-split/entropy
-- identification on that same carrier.
rOperationPublishedPolymerDictionaryLevel : ProofLevel
rOperationPublishedPolymerDictionaryLevel =
  RSupport.cmp122ROperationPublishedPolymerToPeriodicCarrierLevel

rOperationWeightSplitAndRootedEntropyLevel : ProofLevel
rOperationWeightSplitAndRootedEntropyLevel = conditional

-- B localization is source-owned, but its published X must still be identified
-- with the periodic polymer before the selected shell embedding is same-object.
boundaryPublishedPolymerDictionaryLevel : ProofLevel
boundaryPublishedPolymerDictionaryLevel =
  BSupport.cmp119BoundaryPublishedPolymerToPeriodicCarrierLevel

boundaryLocalizedTermsToSelectedShellsLevel : ProofLevel
boundaryLocalizedTermsToSelectedShellsLevel = conditional

vacuumEvaluatorIsSourceConstantLevel : ProofLevel
vacuumEvaluatorIsSourceConstantLevel =
  RP.cmp119VacuumActionEvaluatorConstantIdentificationLevel

-- E remains the asymmetric sector in the representation layer: the current
-- exact source form exposes `Component`, not a component->periodic-polymer
-- support map.  That map must be source-written before E can share the B/R OS
-- classifier and the final common shell carrier.
regularEComponentToPeriodicPolymerSupportLevel : ProofLevel
regularEComponentToPeriodicPolymerSupportLevel = conditional

fullResidualEqualsSelectedFiniteShellTailLevel : ProofLevel
fullResidualEqualsSelectedFiniteShellTailLevel = conditional
