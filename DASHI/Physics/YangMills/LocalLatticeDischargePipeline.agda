module DASHI.Physics.YangMills.LocalLatticeDischargePipeline where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)
open import Data.Nat.Base using (ℕ; _≤_)
open import DASHI.Core.Prelude using (_×_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; -ℝ_; _-ℝ_)
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

import DASHI.Physics.YangMills.GraphCombinatorics as GraphCombinatorics
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.StepVAssemblyLemmaQueue as Assembly

Nat : Set
Nat = ℕ

-- Synonym for entropy/decay margin
ExplicitEntropyDecayMargin : Set₁
ExplicitEntropyDecayMargin = Entropy.P09EntropyMarginDischargePackage

-- Synonym for P10 large-field analytic leaves
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
    p06ModelLeaves : Entropy.P06ModelLeafDischargePackage
    p10AnalyticLeaves : P10AnalyticLeaves
    p33PerturbationStability : GraphCombinatorics.P33a1AnalyticDischargePackage
    entropyDecayMargin : ExplicitEntropyDecayMargin
    p08p11Positivity : P08P11AbsorptionPackageType
    natPowerDecay : NatPowerDecayMonotoneType
    complexityDiameter : ComplexityLowerBoundByDiameterForDecayType
    noClayPromotion : clayYangMillsPromoted ≡ false

postulate
  postulatedLocalLatticeStepVFromAnalyticDischarge :
    LocalLatticeAnalyticDischargePackage
    → Assembly.StepVSpatialKPCertificate

LocalLatticeStepVFromAnalyticDischarge :
  LocalLatticeAnalyticDischargePackage
  → Assembly.StepVSpatialKPCertificate
LocalLatticeStepVFromAnalyticDischarge pkg = postulatedLocalLatticeStepVFromAnalyticDischarge pkg

postulate
  postulatedYangMillsEndpointFromLocalLatticeAndTransferPackages :
    LocalLatticeAnalyticDischargePackage
    → Assembly.P12P19RGTransferPackage
    → Assembly.FixedLatticeGapDischargePackage
    → Assembly.ThermodynamicLimitPackage
    → Assembly.ContinuumLimitPackage
    → Assembly.OSWightmanEndpointPackage
    → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap

YangMillsEndpointFromLocalLatticeAndTransferPackages :
  LocalLatticeAnalyticDischargePackage
  → Assembly.P12P19RGTransferPackage
  → Assembly.FixedLatticeGapDischargePackage
  → Assembly.ThermodynamicLimitPackage
  → Assembly.ContinuumLimitPackage
  → Assembly.OSWightmanEndpointPackage
  → Assembly.YangMillsQuantumFieldTheory × Assembly.PhysicalMassGap
YangMillsEndpointFromLocalLatticeAndTransferPackages localPkg rgPkg gapPkg thermoPkg contPkg osPkg =
  postulatedYangMillsEndpointFromLocalLatticeAndTransferPackages localPkg rgPkg gapPkg thermoPkg contPkg osPkg

localLatticeNoClayPromotion :
  LocalLatticeAnalyticDischargePackage
  → clayYangMillsPromoted ≡ false
localLatticeNoClayPromotion pkg = LocalLatticeAnalyticDischargePackage.noClayPromotion pkg
