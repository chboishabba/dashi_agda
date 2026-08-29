module DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact where

------------------------------------------------------------------------
-- ROUND68: FIVE THEOREM ROLES -> LITERAL CLAY EVIDENCE
--
-- This module does NOT resurrect a leaf-count architecture.  Its purpose is a
-- falsifiable coverage test for the Round67 top-down object: if the five
-- theorem-sized mathematical conclusions proposed by the current programme are
-- really sufficient, they must directly inhabit EVERY official requirement of
-- `LiteralClayEvidence Y` on one and the same construction Y.
--
-- The five theorem roles are therefore records of concrete predicates on Y,
-- never arbitrary Sets:
--
--   LiteralWeakCouplingRGConstruction
--   CutoffUniformPhysicalMassGap
--   UnifiedContinuumYMConstruction
--   ContinuumLocalFieldOPEStressWard
--   InteractingContinuumNontriviality
--
-- Compact-simple classification and four-dimensional spacetime are structural
-- endpoint data rather than another analytic theorem.  All group-dependent
-- analytic work is quantified over the SAME `CompactSimpleGroup` carrier from
-- the outset; there is no downstream promotion arrow.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

------------------------------------------------------------------------
-- Structural endpoint data: not a sixth physical analysis theorem.
------------------------------------------------------------------------

record LiteralClayStructuralBase
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    compactSimple : ∀ G → Top.IsCompactSimple S G
    fourDimensionalEuclidean :
      Top.IsFourDimensionalEuclidean S (Top.spacetime Y)
    compactSimpleParameterization :
      Top.CompactSimpleParameterizationPreserved S
open LiteralClayStructuralBase public

------------------------------------------------------------------------
-- T1. Literal weak-coupling RG construction on the finite-cutoff family.
------------------------------------------------------------------------

record LiteralWeakCouplingRGConstruction
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    finiteVolumeCutoffMeasure : ∀ G cutoff →
      Top.IsFiniteVolumeCutoffMeasure S G cutoff
        (Top.finiteMeasure Y G cutoff)

    reflectionPositiveRegularization : ∀ G cutoff →
      Top.IsReflectionPositiveRegularization S G cutoff
        (Top.finiteMeasure Y G cutoff)

    ultravioletYangMillsNormalization : ∀ G →
      Top.HasUltravioletYangMillsNormalization S G (Top.finiteMeasure Y G)

    asymptoticallyFreeScaleTrajectory : ∀ G →
      Top.HasAsymptoticallyFreeScaleTrajectory S G (Top.finiteMeasure Y G)

    gaugeSymmetryPreserved : ∀ G →
      Top.GaugeSymmetryPreservedAlongConstruction S G
    localityPreserved : ∀ G →
      Top.LocalityPreservedAlongConstruction S G
    euclideanCovariancePreserved : ∀ G →
      Top.EuclideanCovariancePreservedAlongConstruction S G
    reflectionPositivityPreserved : ∀ G →
      Top.ReflectionPositivityPreservedAlongConstruction S G
    positivityNormalizationPreserved : ∀ G →
      Top.PositivityNormalizationPreservedAlongConstruction S G
    volumeCutoffCompatibility : ∀ G →
      Top.VolumeCutoffCompatibilityPreserved S G
open LiteralWeakCouplingRGConstruction public

------------------------------------------------------------------------
-- T2. Cutoff-uniform physical mass gap on the reconstructed Hamiltonian.
------------------------------------------------------------------------

record CutoffUniformPhysicalMassGap
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    vacuumSectorAndPositiveEnergyComplement : ∀ G →
      Top.IsVacuumSectorAndPositiveEnergyComplement S
        (Top.hilbertSpace Y G) (Top.hamiltonian Y G) (Top.vacuum Y G)

    strictlyPositiveFiniteMassGap : ∀ G →
      Top.IsStrictlyPositiveFiniteMassGap S
        (Top.hamiltonian Y G) (Top.massGap Y G)

    physicalScaleLowerBoundUniform : ∀ G →
      Top.PhysicalScaleLowerBoundUniform S G (Top.massGap Y G)

    noSpectralPollutionBelowGap : ∀ G →
      Top.NoSpectralPollutionBelowGap S G
        (Top.hamiltonian Y G) (Top.massGap Y G)

    gapAndClusteringDerived : ∀ G →
      Top.GapAndClusteringAreDerivedNotAssumed S G
open CutoffUniformPhysicalMassGap public

------------------------------------------------------------------------
-- T3. Unified continuum construction: the SAME finite family has one
-- continuum measure, its Schwinger family, accepted OS/Wightman strength, and
-- reconstructed positive self-adjoint Hamiltonian.
------------------------------------------------------------------------

record UnifiedContinuumYMConstruction
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    continuumLimit : ∀ G →
      Top.IsContinuumLimitOf S G
        (Top.finiteMeasure Y G) (Top.continuumMeasure Y G)

    schwingerBelongsToContinuumMeasure : ∀ G →
      Top.SchwingerBelongsToMeasure S
        (Top.continuumMeasure Y G) (Top.schwinger Y G)

    acceptedWightmanOrOSAxioms : ∀ G →
      Top.SatisfiesAcceptedWightmanOrOSAxioms S G (Top.schwinger Y G)

    reconstructedHilbertSpace : ∀ G →
      Top.IsReconstructedHilbertSpace S G
        (Top.schwinger Y G) (Top.hilbertSpace Y G)

    positiveSelfAdjointHamiltonian : ∀ G →
      Top.IsPositiveSelfAdjointHamiltonian S
        (Top.hilbertSpace Y G) (Top.hamiltonian Y G)
open UnifiedContinuumYMConstruction public

------------------------------------------------------------------------
-- T4. Local curvature fields, concrete OPE data, stress tensor and short-
-- distance AF matching, all on the same continuum family.
------------------------------------------------------------------------

record ContinuumLocalFieldOPEStressWard
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    gaugeInvariantLocalObservable : ∀ G position →
      Top.IsGaugeInvariantObservable S (Top.localObservable Y G position)
      × Top.IsLocalObservable S (Top.localObservable Y G position) position

    curvatureOperatorCorrespondence : ∀ G →
      Top.CurvatureOperatorCorrespondence S G (Top.curvatureOperator Y G)

    curvatureOperatorsGaugeInvariant : ∀ G polynomial →
      Top.IsGaugeInvariantLocalOperator S (Top.curvatureOperator Y G polynomial)

    curvatureOperatorsLocal : ∀ G polynomial position →
      Top.IsLocalOperator S (Top.curvatureOperator Y G polynomial) position

    shortDistanceAsymptoticFreedom : ∀ G →
      Top.HasShortDistanceAsymptoticFreedom S G (Top.schwinger Y G)

    stressTensorAndOPE : ∀ G →
      Top.HasStressTensorAndOPE S G
        (Top.schwinger Y G) (Top.stressTensor Y G)

    physicalOPECoefficient : ∀ G left right output position →
      Top.IsPhysicalOPECoefficient S G left right output position
        (Top.opeCoefficient Y G left right output position)

    physicalOPERemainder : ∀ G left right position depth →
      Top.IsPhysicalOPERemainder S G left right position depth
        (Top.opeRemainder Y G left right position depth)
open ContinuumLocalFieldOPEStressWard public

------------------------------------------------------------------------
-- T5. Same-limit interacting/non-Gaussian survival.
------------------------------------------------------------------------

record InteractingContinuumNontriviality
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    nontrivialQuantumYangMills : ∀ G →
      Top.IsNontrivialQuantumYangMills S G
        (Top.continuumMeasure Y G) (Top.schwinger Y G)

    nontrivialityPreservedInLimit : ∀ G →
      Top.NontrivialityPreservedInLimit S G (Top.continuumMeasure Y G)
open InteractingContinuumNontriviality public

------------------------------------------------------------------------
-- Requirement-by-requirement compiler.  Every branch returns the literal type
-- demanded by Round67; no endpoint-identification postulate is available.
------------------------------------------------------------------------

preconditionsFromFive :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralClayStructuralBase Y →
  LiteralWeakCouplingRGConstruction Y →
  UnifiedContinuumYMConstruction Y →
  ContinuumLocalFieldOPEStressWard Y →
  ∀ requirement → Top.preconditionRequirement Y requirement
preconditionsFromFive structural rg continuum local Clay.compactSimpleGaugeGroupIndex =
  compactSimple structural
preconditionsFromFive structural rg continuum local Clay.fourDimensionalEuclideanSpacetime =
  fourDimensionalEuclidean structural
preconditionsFromFive structural rg continuum local Clay.gaugeInvariantLocalObservableFamily =
  gaugeInvariantLocalObservable local
preconditionsFromFive structural rg continuum local Clay.finiteVolumeCutoffMeasureFamily =
  finiteVolumeCutoffMeasure rg
preconditionsFromFive structural rg continuum local Clay.reflectionPositiveRegularization =
  reflectionPositiveRegularization rg
preconditionsFromFive structural rg continuum local Clay.ultravioletYangMillsNormalization =
  ultravioletYangMillsNormalization rg
preconditionsFromFive structural rg continuum local Clay.asymptoticallyFreeScaleTrajectory =
  asymptoticallyFreeScaleTrajectory rg
preconditionsFromFive structural rg continuum local Clay.acceptedAxiomaticQFTTarget =
  acceptedWightmanOrOSAxioms continuum

postconditionsFromFive :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralClayStructuralBase Y →
  UnifiedContinuumYMConstruction Y →
  CutoffUniformPhysicalMassGap Y →
  ContinuumLocalFieldOPEStressWard Y →
  InteractingContinuumNontriviality Y →
  ∀ requirement → Top.postconditionRequirement Y requirement
postconditionsFromFive structural continuum gap local interacting
    Clay.nontrivialQuantumYangMillsTheoryOnR4 =
  λ G →
    continuumLimit continuum G ,
    (schwingerBelongsToContinuumMeasure continuum G ,
     nontrivialQuantumYangMills interacting G)
postconditionsFromFive structural continuum gap local interacting
    Clay.gaugeInvariantCurvatureOperatorCorrespondence =
  λ G →
    curvatureOperatorCorrespondence local G ,
    ((λ polynomial → curvatureOperatorsGaugeInvariant local G polynomial) ,
     (λ polynomial position → curvatureOperatorsLocal local G polynomial position))
postconditionsFromFive structural continuum gap local interacting
    Clay.shortDistanceAsymptoticFreedomAgreement =
  shortDistanceAsymptoticFreedom local
postconditionsFromFive structural continuum gap local interacting
    Clay.stressTensorAndOperatorProductExpansion =
  λ G →
    stressTensorAndOPE local G ,
    ((λ left right output position →
       physicalOPECoefficient local G left right output position) ,
     (λ left right position depth →
       physicalOPERemainder local G left right position depth))
postconditionsFromFive structural continuum gap local interacting
    Clay.acceptedWightmanOrOSStrengthAxioms =
  acceptedWightmanOrOSAxioms continuum
postconditionsFromFive structural continuum gap local interacting
    Clay.reconstructedPositiveSelfAdjointHamiltonian =
  λ G →
    reconstructedHilbertSpace continuum G ,
    positiveSelfAdjointHamiltonian continuum G
postconditionsFromFive structural continuum gap local interacting
    Clay.vacuumSectorAndPositiveEnergyComplement =
  vacuumSectorAndPositiveEnergyComplement gap
postconditionsFromFive structural continuum gap local interacting
    Clay.strictlyPositiveFiniteMassGap =
  strictlyPositiveFiniteMassGap gap
postconditionsFromFive structural continuum gap local interacting
    Clay.constructionForEveryCompactSimpleGaugeGroup =
  λ G isCompact → continuumLimit continuum G

invariantsFromFive :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralClayStructuralBase Y →
  LiteralWeakCouplingRGConstruction Y →
  CutoffUniformPhysicalMassGap Y →
  InteractingContinuumNontriviality Y →
  ∀ requirement → Top.invariantRequirement Y requirement
invariantsFromFive structural rg gap interacting Clay.gaugeSymmetryPreserved =
  gaugeSymmetryPreserved rg
invariantsFromFive structural rg gap interacting Clay.localityPreserved =
  localityPreserved rg
invariantsFromFive structural rg gap interacting Clay.euclideanCovariancePreserved =
  euclideanCovariancePreserved rg
invariantsFromFive structural rg gap interacting Clay.reflectionPositivityPreserved =
  reflectionPositivityPreserved rg
invariantsFromFive structural rg gap interacting Clay.measurePositivityAndNormalizationPreserved =
  positivityNormalizationPreserved rg
invariantsFromFive structural rg gap interacting Clay.volumeAndCutoffCompatibilityPreserved =
  volumeCutoffCompatibility rg
invariantsFromFive structural rg gap interacting Clay.physicalScaleLowerBoundUniform =
  physicalScaleLowerBoundUniform gap
invariantsFromFive structural rg gap interacting Clay.noSpectralPollutionBelowGap =
  noSpectralPollutionBelowGap gap
invariantsFromFive structural rg gap interacting Clay.nontrivialityPreservedInTheLimit =
  nontrivialityPreservedInLimit interacting
invariantsFromFive structural rg gap interacting Clay.targetGapAndClusteringNotAssumedAsInputs =
  gapAndClusteringDerived gap
invariantsFromFive structural rg gap interacting Clay.compactSimpleGroupParameterizationPreserved =
  compactSimpleParameterization structural

literalClayEvidenceFromFiveTheorems :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  LiteralClayStructuralBase Y →
  LiteralWeakCouplingRGConstruction Y →
  CutoffUniformPhysicalMassGap Y →
  UnifiedContinuumYMConstruction Y →
  ContinuumLocalFieldOPEStressWard Y →
  InteractingContinuumNontriviality Y →
  Top.LiteralClayEvidence Y
literalClayEvidenceFromFiveTheorems Y structural rg gap continuum local interacting = record
  { Top.LiteralClayEvidence.preconditions =
      preconditionsFromFive structural rg continuum local
  ; Top.LiteralClayEvidence.postconditions =
      postconditionsFromFive structural continuum gap local interacting
  ; Top.LiteralClayEvidence.invariants =
      invariantsFromFive structural rg gap interacting
  }

literalClaySolutionFromFiveTheorems :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  LiteralClayStructuralBase Y →
  LiteralWeakCouplingRGConstruction Y →
  CutoffUniformPhysicalMassGap Y →
  UnifiedContinuumYMConstruction Y →
  ContinuumLocalFieldOPEStressWard Y →
  InteractingContinuumNontriviality Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromFiveTheorems Y structural rg gap continuum local interacting =
  Top.literalTopDownClaySolution Y
    (literalClayEvidenceFromFiveTheorems
      Y structural rg gap continuum local interacting)

topDownFiveTheoremCoverageCompilerLevel : ProofLevel
topDownFiveTheoremCoverageCompilerLevel = machineChecked

-- No physical inhabitant is supplied here.  Each theorem role above is an
-- exact property of the same Y and remains to be constructed from the source-
-- native Balaban/SZZ/BDH/OS/local-field mathematics.
physicalTopDownFiveTheoremInstantiationLevel : ProofLevel
physicalTopDownFiveTheoremInstantiationLevel = conditional
