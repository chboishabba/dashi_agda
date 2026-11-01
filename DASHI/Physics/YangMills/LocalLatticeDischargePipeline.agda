module DASHI.Physics.YangMills.LocalLatticeDischargePipeline where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _≤_)
open import DASHI.Core.Prelude using (_×_; false)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; -ℝ_; _-ℝ_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; VerificationStatus
  ; dashi-internal-proof
  ; mixedReducer
  )

import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as Anisotropic
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly

Nat : Set
Nat = ℕ

-- Synonym for entropy/decay margin
ExplicitEntropyDecayMargin : Set₁
ExplicitEntropyDecayMargin = Entropy.P09EntropyMarginDischargePackage

-- Synonym for the owned P10 large-field analytic leaf package
P10AnalyticLeaves : Set₁
P10AnalyticLeaves = LargeField.P10AnalyticLeaves

-- Synonym for P08/P11 absorption package type
P08P11AbsorptionPackageType : Set₁
P08P11AbsorptionPackageType =
  ∀ (k : Nat) (X : List Nat) → GraphCombinatorics.P08P11AbsorptionPackage k X

-- Type for Nat/power decay monotonicity
NatPowerDecayMonotoneType : Set
NatPowerDecayMonotoneType =
  ∀ (a b : Nat) (c : ℝ) → 0ℝ ≤ℝ c → c ≤ℝ 1ℝ → a ≤ b
  → (c LargeField.^ℝ (LargeField.fromNat b)) ≤ℝ (c LargeField.^ℝ (LargeField.fromNat a))

-- Type for ComplexityLowerBoundByDiameterForDecay
ComplexityLowerBoundByDiameterForDecayType : Set
ComplexityLowerBoundByDiameterForDecayType =
  ∀ (X : List Nat) (diamPolyNat : List Nat → Nat) → LargeField.ComplexityLowerBoundByDiameterForDecay X diamPolyNat

record LocalLatticeAnalyticDischargePackage : Set₁ where
  field
    p06MixedReducerPayload : Entropy.BalabanP06MixedReducerPayload
    p10AnalyticLeaves : P10AnalyticLeaves
    p33PerturbationStability : Anisotropic.P33a1AnalyticDischargePackage
    entropyDecayMargin : ExplicitEntropyDecayMargin
    p08p11Positivity : P08P11AbsorptionPackageType
    natPowerDecay : NatPowerDecayMonotoneType
    complexityDiameter : ComplexityLowerBoundByDiameterForDecayType
    noClayPromotion : clayYangMillsPromoted ≡ false

LocalLatticeP06SourceKernel :
  LocalLatticeAnalyticDischargePackage →
  Entropy.P06SourceSkeletonDecompositionSemanticKernel
LocalLatticeP06SourceKernel pkg =
  Entropy.P06SourceSkeletonDecompositionSemanticKernelFromPayload
    (LocalLatticeAnalyticDischargePackage.p06MixedReducerPayload pkg)

LocalLatticeP06CountingWitness :
  LocalLatticeAnalyticDischargePackage →
  Entropy.ImportedPolymerAnimalCountingBound
LocalLatticeP06CountingWitness pkg = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "LocalLatticeDischargePipeline.LocalLatticeP06CountingWitness/LocalLatticeDischargePipeline.LocalLatticeP06SourceKernel"
  ; status = mixedReducer
  ; mixedReducerPayload =
      Entropy.P06SourceSkeletonDecompositionSemanticKernel.payload
        (LocalLatticeP06SourceKernel pkg)
  }

LocalLatticeP33DiameterLane :
  (pkg : LocalLatticeAnalyticDischargePackage) →
  Anisotropic.P33DiameterLaneFromAnalyticDischarge
    (LocalLatticeAnalyticDischargePackage.p33PerturbationStability pkg)
LocalLatticeP33DiameterLane pkg =
  Anisotropic.buildP33DiameterLaneFromAnalyticDischarge
    (LocalLatticeAnalyticDischargePackage.p33PerturbationStability pkg)

LocalLatticeStepVSourceInputs :
  LocalLatticeAnalyticDischargePackage →
  Assembly.StepVSourceAnalyticInputs
LocalLatticeStepVSourceInputs pkg = record
  { p06AnimalCounting =
      LocalLatticeP06CountingWitness pkg
  ; p06MixedReducerPayload =
      LocalLatticeAnalyticDischargePackage.p06MixedReducerPayload pkg
  ; p06MixedReducerPayloadMatches = refl
  ; p10LargeFieldActivity =
      LargeField.P10CurrentCanonicalLargeFieldDecayFromOwnedKernels
  ; p11AbsorptionCondition =
      LargeField.postulatedAbsorptionConditionWitness
  ; p33aUniformLinkEllipticity =
      Anisotropic.P33DiameterLaneFromAnalyticDischarge.p33aWrapper
        (LocalLatticeP33DiameterLane pkg)
  }

LocalLatticeStepVSourceInputsMatchOwnedP06EndpointKernelPayload :
  ∀ pkg →
  Assembly.StepVSourceAnalyticInputs.p06MixedReducerPayload
    (LocalLatticeStepVSourceInputs pkg)
    ≡ Entropy.P06SourceSkeletonDecompositionSemanticKernel.payload
        (LocalLatticeP06SourceKernel pkg)
LocalLatticeStepVSourceInputsMatchOwnedP06EndpointKernelPayload pkg = refl

LocalLatticeStepVInternalReducers :
  LocalLatticeAnalyticDischargePackage →
  Assembly.StepVInternalReducers
LocalLatticeStepVInternalReducers pkg = record
  { p33bDiameterDomination =
      Anisotropic.P33DiameterLaneFromAnalyticDischarge.p33bTheorem
        (LocalLatticeP33DiameterLane pkg)
  ; p07KPSummabilityReducer =
      Assembly.stepVP07Reducer
  ; p09EntropyMarginReducer =
      Assembly.stepVP09Reducer
  }

LocalLatticeStepVFromAnalyticDischarge :
  LocalLatticeAnalyticDischargePackage
  → Assembly.StepVSpatialKPCertificate
LocalLatticeStepVFromAnalyticDischarge pkg =
  Assembly.StepVFromDischargePackages
    (LocalLatticeStepVSourceInputs pkg)
    (LocalLatticeStepVInternalReducers pkg)

LocalLatticeStepVToRGDischarge :
  Assembly.P12P19RGTransferPackage →
  Assembly.StepVToRGDischargePackage
LocalLatticeStepVToRGDischarge =
  Assembly.StepVToRGDischargePackageFromP12P19

LocalLatticeFixedLatticeMassGapPackage :
  Assembly.FixedLatticeGapDischargePackage →
  Assembly.FixedLatticeMassGapPackage
LocalLatticeFixedLatticeMassGapPackage gapPkg = record
  { spectralGap =
      Assembly.FixedLatticeGapDischargePackage.lsiToSpectralGap gapPkg
        (Assembly.FixedLatticeGapDischargePackage.uniformLSI gapPkg)
  ; proofBoundary =
      "FixedLatticeMassGapPackage: packages the positive spectral gap verified on a fixed lattice."
  ; proofBoundaryIsCanonical = refl
  ; noClayPromotion =
      Assembly.FixedLatticeGapDischargePackage.noClayPromotion gapPkg
  }

record StepVDownstreamInternalisationKernel : Set₁ where
  field
    sourceAuthorityId :
      SourceAuthorityId

    theoremLocator :
      String

    status :
      VerificationStatus

    localLatticeStepV :
      LocalLatticeAnalyticDischargePackage
      → Assembly.StepVSpatialKPCertificate

    yangMillsEndpoint :
      LocalLatticeAnalyticDischargePackage
      → Assembly.P12P19RGTransferPackage
      → Assembly.FixedLatticeGapDischargePackage
      → Assembly.ThermodynamicLimitPackage
      → Assembly.ContinuumLimitPackage
      → Assembly.OSWightmanEndpointPackage
      → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap

    noClayPromotion :
      clayYangMillsPromoted ≡ false

YangMillsEndpointFromLocalLatticeAndTransferPackages :
  LocalLatticeAnalyticDischargePackage
  → Assembly.P12P19RGTransferPackage
  → Assembly.FixedLatticeGapDischargePackage
  → Assembly.ThermodynamicLimitPackage
  → Assembly.ContinuumLimitPackage
  → Assembly.OSWightmanEndpointPackage
  → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
YangMillsEndpointFromLocalLatticeAndTransferPackages localPkg rgPkg gapPkg thermoPkg contPkg osPkg =
  Assembly.ConditionalYangMillsPipelineFromDischargePackages
    (LocalLatticeStepVSourceInputs localPkg)
    (LocalLatticeStepVInternalReducers localPkg)
    (LocalLatticeStepVToRGDischarge rgPkg)
    (LocalLatticeFixedLatticeMassGapPackage gapPkg)
    thermoPkg
    contPkg
    osPkg

currentStepVDownstreamInternalisationKernel :
  StepVDownstreamInternalisationKernel
currentStepVDownstreamInternalisationKernel = record
  { sourceAuthorityId = dashi-internal-proof
  ; theoremLocator =
      "LocalLatticeDischargePipeline.{LocalLatticeStepVSourceInputs,LocalLatticeStepVInternalReducers,LocalLatticeStepVFromAnalyticDischarge,YangMillsEndpointFromLocalLatticeAndTransferPackages}; P06 enters through the owned current P06 endpoint kernel and current P06 mixed-reducer path, P10 enters through LargeField.P10CurrentCanonicalLargeFieldDecayFromOwnedKernels, while P11 and downstream transfer/endpoint packages retain the remaining external authority boundary."
  ; status = mixedReducer
  ; localLatticeStepV =
      LocalLatticeStepVFromAnalyticDischarge
  ; yangMillsEndpoint =
      YangMillsEndpointFromLocalLatticeAndTransferPackages
  ; noClayPromotion = refl
  }

localLatticeNoClayPromotion :
  LocalLatticeAnalyticDischargePackage
  → clayYangMillsPromoted ≡ false
localLatticeNoClayPromotion pkg = LocalLatticeAnalyticDischargePackage.noClayPromotion pkg
