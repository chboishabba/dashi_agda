module DASHI.Economics.AICoreWeaveDDTL4PolarisForgeMapping20261016Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secKind : Source.SourceKind
secKind = Source.namedSourceKind "SEC-filed financing / landlord lease disclosure"

coreWeaveDDTL4Source : Source.AttributedSource
coreWeaveDDTL4Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "DDTL 4.0 Credit Agreement, Exhibit 10.1"
  "SEC filing"
  "2026-03-30"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000129/ex1011.htm"
  secKind
  "names CoreWeave Compute Acquisition Co. VIII, LLC as borrower under the USD8.5B GPU/infrastructure financing"
  Source.publicAttribution

appliedDigitalPolarisForgeSource : Source.AttributedSource
appliedDigitalPolarisForgeSource = Source.mkNoDOISource
  "Applied Digital Corporation"
  "Annual report for fiscal year ended May 31 2026"
  "SEC filing"
  "2026-08"
  "https://www.sec.gov/Archives/edgar/data/1144879/000114487926000048/apld-20260531.htm"
  secKind
  "identifies CoreWeave Compute Acquisition Co. VIII, LLC as the CoreWeave SPV tenant/assignee for Polaris Forge 1 Building 2 partial data halls and Building 3 lease; Building 2 is 100MW and Building 3 is 150MW at campus level, but the financing-specific MW allocation is not disclosed"
  Source.publicAttribution

record DDTL4PolarisForgeMapping : Set where
  constructor ddtl4-polaris-forge-mapping
  field
    sameBorrowerSPV : Bool
    polarisForge1SiteIdentity : Bool
    building2And3LeaseLink : Bool
    exactFinancedMW : Bool
    financedGPUGeneration : Bool
    financedGPUCount : Bool
    financedCustomerIdentity : Bool
    realisedProjectCashReturn : Bool

open DDTL4PolarisForgeMapping public

coreWeaveDDTL4PolarisForgeMapping : DDTL4PolarisForgeMapping
coreWeaveDDTL4PolarisForgeMapping = ddtl4-polaris-forge-mapping
  true true true false false false false false

sameBorrowerSPVIsPaid : sameBorrowerSPV coreWeaveDDTL4PolarisForgeMapping ≡ true
sameBorrowerSPVIsPaid = refl

polarisForge1SiteIdentityPaid : polarisForge1SiteIdentity coreWeaveDDTL4PolarisForgeMapping ≡ true
polarisForge1SiteIdentityPaid = refl

building2And3LeaseLinkPaid : building2And3LeaseLink coreWeaveDDTL4PolarisForgeMapping ≡ true
building2And3LeaseLinkPaid = refl

exactFinancedMWStillOpen : exactFinancedMW coreWeaveDDTL4PolarisForgeMapping ≡ false
exactFinancedMWStillOpen = refl

gpuGenerationStillOpen : financedGPUGeneration coreWeaveDDTL4PolarisForgeMapping ≡ false
gpuGenerationStillOpen = refl

customerIdentityStillOpen : financedCustomerIdentity coreWeaveDDTL4PolarisForgeMapping ≡ false
customerIdentityStillOpen = refl

boundary : String
boundary =
  "A same-entity finance-to-site weld is now paid for DDTL 4.0. CoreWeave's filed agreement names CoreWeave Compute Acquisition Co. VIII, LLC as the GPU/infrastructure financing borrower; Applied Digital's filing names that same SPV as tenant/assignee for Polaris Forge 1 Building 2 partial data halls and Building 3. This narrows the asset-mapping residual from company-level to a named SPV/site/lease object. The public evidence does not identify the exact MW financed by DDTL 4.0, the GPU generation/count installed in those financed spaces, the associated customer identity, or realised project cash return."
