module DASHI.Physics.Closure.NSTriadKNLuoFullCompletionLemmaInventoryExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Charles L. Fefferman; Clay Mathematics Institute.
-- Title: "Existence and Smoothness of the Navier--Stokes Equation".
-- Millennium Prize Problems, 2000.
-- DOI: not assigned to the official problem description.
--
-- PURPOSE
-- Assemble all 15 stage-qualified lemma families between the current
-- source-faithful Luo frontier and a submission-ready periodic theorem.
--
-- The source analysis contains 661 stage-qualified occurrences representing
-- 659 unique lemma names. A FullLuoCompletionInhabitants value must prove the
-- actual proposition assigned to every occurrence. Current repository status
-- remains deliberately fail-closed.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryAExact as A
import DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryBExact as B
import DASHI.Physics.Closure.NSTriadKNLuoCompletionLemmaInventoryCExact as C
import DASHI.Physics.Closure.NSTriadKNLuoCanonicalAnalyticInputsBuilderExact as Builder
import DASHI.Physics.Closure.NSTriadKNLuoCompleteSubmissionCompositionExact as Final

record FullLuoCompletionSpecifications : Setω where
  field
    fourierCarrierSpecification : A.Stage0.Specification
    weightedSpatialFourierSpecification : A.Stage1.Specification
    physicalPairCoefficientSpecification : A.Stage2.Specification
    officialMultiplierReceiptSpecification : A.Stage3.Specification
    physicalSourceSchurSpecification : A.Stage4.Specification
    equation42Specification : B.Stage5.Specification
    section4Specification : B.Stage6.Specification
    realFractionalGronwallSpecification : B.Stage7.Specification
    cutoffCorrectionDecaySpecification : B.Stage8.Specification
    officialShellMaximalTimeSpecification : B.Stage9.Specification
    infiniteRealPromotionSpecification : C.Stage10.Specification
    uniformStrongSolutionSpecification : C.Stage11.Specification
    sobolevPressureSpecification : C.Stage12.Specification
    submissionAuditSpecification : C.Stage13.Specification
    problemScopeNormalizationSpecification : C.Stage14.Specification

open FullLuoCompletionSpecifications public

record FullLuoCompletionInhabitants
    (specifications : FullLuoCompletionSpecifications) : Setω where
  field
    fourierCarrierProofs :
      A.Stage0.Inhabitants
        (fourierCarrierSpecification specifications)
    weightedSpatialFourierProofs :
      A.Stage1.Inhabitants
        (weightedSpatialFourierSpecification specifications)
    physicalPairCoefficientProofs :
      A.Stage2.Inhabitants
        (physicalPairCoefficientSpecification specifications)
    officialMultiplierReceiptProofs :
      A.Stage3.Inhabitants
        (officialMultiplierReceiptSpecification specifications)
    physicalSourceSchurProofs :
      A.Stage4.Inhabitants
        (physicalSourceSchurSpecification specifications)
    equation42Proofs :
      B.Stage5.Inhabitants
        (equation42Specification specifications)
    section4Proofs :
      B.Stage6.Inhabitants
        (section4Specification specifications)
    realFractionalGronwallProofs :
      B.Stage7.Inhabitants
        (realFractionalGronwallSpecification specifications)
    cutoffCorrectionDecayProofs :
      B.Stage8.Inhabitants
        (cutoffCorrectionDecaySpecification specifications)
    officialShellMaximalTimeProofs :
      B.Stage9.Inhabitants
        (officialShellMaximalTimeSpecification specifications)
    infiniteRealPromotionProofs :
      C.Stage10.Inhabitants
        (infiniteRealPromotionSpecification specifications)
    uniformStrongSolutionProofs :
      C.Stage11.Inhabitants
        (uniformStrongSolutionSpecification specifications)
    sobolevPressureProofs :
      C.Stage12.Inhabitants
        (sobolevPressureSpecification specifications)
    submissionAuditProofs :
      C.Stage13.Inhabitants
        (submissionAuditSpecification specifications)
    problemScopeNormalizationProofs :
      C.Stage14.Inhabitants
        (problemScopeNormalizationSpecification specifications)

open FullLuoCompletionInhabitants public

record LuoApprovedConstantDependencies : Set₁ where
  field
    MultiplierConstantDependsOnlyOnCutoffAndDimension : Set
    multiplierConstantDependsOnlyOnCutoffAndDimension :
      MultiplierConstantDependsOnlyOnCutoffAndDimension

    SchurConstantDependsOnlyOnApprovedProfileData : Set
    schurConstantDependsOnlyOnApprovedProfileData :
      SchurConstantDependsOnlyOnApprovedProfileData

    Section4ConstantsDependOnlyOnApprovedParameters : Set
    section4ConstantsDependOnlyOnApprovedParameters :
      Section4ConstantsDependOnlyOnApprovedParameters

    GronwallConstantsDependOnlyOnApprovedParameters : Set
    gronwallConstantsDependOnlyOnApprovedParameters :
      GronwallConstantsDependOnlyOnApprovedParameters

    NoShellDependence : Set
    noShellDependence : NoShellDependence

    NoTruncationDependence : Set
    noTruncationDependence : NoTruncationDependence

    NoTerminalTimeDependenceUnlessDeclared : Set
    noTerminalTimeDependenceUnlessDeclared :
      NoTerminalTimeDependenceUnlessDeclared

    NoUnknownFutureRegularityDependence : Set
    noUnknownFutureRegularityDependence :
      NoUnknownFutureRegularityDependence

    AllConstantsFinite : Set
    allConstantsFinite : AllConstantsFinite

    AllMajorantConstantsNonnegative : Set
    allMajorantConstantsNonnegative : AllMajorantConstantsNonnegative

    AllAbsorptionThresholdsStrictlyPositive : Set
    allAbsorptionThresholdsStrictlyPositive :
      AllAbsorptionThresholdsStrictlyPositive

open LuoApprovedConstantDependencies public

record LuoFailureModeAudit : Set₁ where
  field
    AlphaOneEndpointFailureCharacterized : Set
    alphaOneEndpointFailureCharacterized :
      AlphaOneEndpointFailureCharacterized

    ShellEndpointFailureCharacterized : Set
    shellEndpointFailureCharacterized :
      ShellEndpointFailureCharacterized

    NonunitKernelMassEffectCharacterized : Set
    nonunitKernelMassEffectCharacterized :
      NonunitKernelMassEffectCharacterized

    HardSmoothSupportShiftEffectCharacterized : Set
    hardSmoothSupportShiftEffectCharacterized :
      HardSmoothSupportShiftEffectCharacterized

    ZeroViscosityFailureCharacterized : Set
    zeroViscosityFailureCharacterized :
      ZeroViscosityFailureCharacterized

    NonMeanZeroCaseCharacterized : Set
    nonMeanZeroCaseCharacterized : NonMeanZeroCaseCharacterized

    WeakSolutionRegularityBoundaryCharacterized : Set
    weakSolutionRegularityBoundaryCharacterized :
      WeakSolutionRegularityBoundaryCharacterized

open LuoFailureModeAudit public

completionLemmaOccurrenceCount : Nat
completionLemmaOccurrenceCount = 661

completionLemmaUniqueNameCount : Nat
completionLemmaUniqueNameCount = 659

completionLemmaStageQualifiedDigest : String
completionLemmaStageQualifiedDigest =
  "sha256:9f6bcf08a4acbb12009f74531fb0ba9919e6a788acf230d541d4efffa8484ecf"

canonicalAnalyticInputBuilderReused : Bool
canonicalAnalyticInputBuilderReused =
  Builder.canonicalAnalyticInputsBuilderConstructed

submissionReadyCompositionReused : Bool
submissionReadyCompositionReused =
  Final.submissionReadyTheoremCompositionConstructed

fullCompletionLemmaInventoryConstructed : Bool
fullCompletionLemmaInventoryConstructed = true

approvedConstantDependencySchemaConstructed : Bool
approvedConstantDependencySchemaConstructed = true

failureModeAuditSchemaConstructed : Bool
failureModeAuditSchemaConstructed = true

fullCompletionLemmaInventoryInhabited : Bool
fullCompletionLemmaInventoryInhabited = false

canonicalAnalyticPhysicalLeavesInhabited : Bool
canonicalAnalyticPhysicalLeavesInhabited = false

periodicNavierStokesGlobalRegularityProved : Bool
periodicNavierStokesGlobalRegularityProved = false

submissionPackageComplete : Bool
submissionPackageComplete = false

canonicalAnalyticInputBuilderReusedIsTrue :
  canonicalAnalyticInputBuilderReused ≡ true
canonicalAnalyticInputBuilderReusedIsTrue =
  Builder.canonicalAnalyticInputsBuilderConstructedIsTrue

submissionReadyCompositionReusedIsTrue :
  submissionReadyCompositionReused ≡ true
submissionReadyCompositionReusedIsTrue =
  Final.submissionReadyTheoremCompositionConstructedIsTrue

fullCompletionLemmaInventoryConstructedIsTrue :
  fullCompletionLemmaInventoryConstructed ≡ true
fullCompletionLemmaInventoryConstructedIsTrue = refl

approvedConstantDependencySchemaConstructedIsTrue :
  approvedConstantDependencySchemaConstructed ≡ true
approvedConstantDependencySchemaConstructedIsTrue = refl

failureModeAuditSchemaConstructedIsTrue :
  failureModeAuditSchemaConstructed ≡ true
failureModeAuditSchemaConstructedIsTrue = refl

fullCompletionLemmaInventoryInhabitedIsFalse :
  fullCompletionLemmaInventoryInhabited ≡ false
fullCompletionLemmaInventoryInhabitedIsFalse = refl

periodicNavierStokesGlobalRegularityRemainsFalse :
  periodicNavierStokesGlobalRegularityProved ≡ false
periodicNavierStokesGlobalRegularityRemainsFalse = refl

submissionPackageRemainsIncomplete :
  submissionPackageComplete ≡ false
submissionPackageRemainsIncomplete = refl
