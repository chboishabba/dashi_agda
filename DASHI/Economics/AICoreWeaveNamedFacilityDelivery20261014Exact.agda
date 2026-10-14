module DASHI.Economics.AICoreWeaveNamedFacilityDelivery20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC-filed counterparty disclosure"

coreScientificQ22026Source : Source.AttributedSource
coreScientificQ22026Source = Source.mkNoDOISource
  "Core Scientific, Inc."
  "Q2 FY2026 earnings deck"
  "SEC-filed investor presentation"
  "2026-08"
  "https://www.sec.gov/Archives/edgar/data/1839341/000183934126000012/q2fy26earningsdeck728am.htm"
  secFilingKind
  "primary counterparty carrier for CoreWeave contracted capacity of about 590 MW across five sites and over 430 MW billing as of mid-July 2026; site table reports Denton about 260 MW billing, Dalton about 30 MW billing, Muskogee about 70 MW, Marble about 65 MW and Austin about 20 MW"
  Source.publicAttribution

coreScientificApril2026Source : Source.AttributedSource
coreScientificApril2026Source = Source.mkNoDOISource
  "Core Scientific, Inc."
  "CoreWeave licensing-agreement project timeline"
  "SEC-filed exhibit"
  "2026-04-21"
  "https://www.sec.gov/Archives/edgar/data/1839341/000119312526165121/d149019dex992.htm"
  secFilingKind
  "primary counterparty carrier for site-specific CoreWeave allocations and delivery schedules: Austin 16.5 MW complete, Denton 262 MW starting delivery complete with H2-2026 substantial completion, Dalton 1 30 MW H1-2026, Dalton 4 145 MW H2-2026/H1-2027, Marble 65 MW complete/H1-2026 completion, Muskogee 70 MW H1-2026"
  Source.publicAttribution

record NamedFacilityDelivery : Set where
  constructor named-facility-delivery
  field
    counterparty : String
    customer : String
    fullContractedHostMW : Nat
    namedBillingFloorMW : Nat
    dentonApproxBillingMW : Nat
    daltonPhaseOneMW : Nat
    muskogeeApproxBillingMW : Nat
    marbleApproxBillingMW : Nat
    austinApproxBillingMW : Nat
    sameMetricAsCoreWeaveActivePower : Bool
    additiveToCoreWeaveActivePowerWithoutReconciliation : Bool
    hardwareGenerationAtEachSitePaid : Bool
    serialHardwareAgePaid : Bool

open NamedFacilityDelivery public

coreScientificCoreWeaveDelivery : NamedFacilityDelivery
coreScientificCoreWeaveDelivery = named-facility-delivery
  "Core Scientific" "CoreWeave"
  590 430
  260 30 70 65 20
  false false false false

namedBillingFloorMWIs430 : namedBillingFloorMW coreScientificCoreWeaveDelivery ≡ 430
namedBillingFloorMWIs430 = refl

daltonPhaseOneMWIs30 : daltonPhaseOneMW coreScientificCoreWeaveDelivery ≡ 30
daltonPhaseOneMWIs30 = refl

fullContractedHostMWIs590 : fullContractedHostMW coreScientificCoreWeaveDelivery ≡ 590
fullContractedHostMWIs590 = refl

data NamedHostCapacityAutoAddsToCoreWeaveActivePowerPermission : Set where
data FacilityDeliveryIdentifiesGPUGenerationPermission : Set where

namedHostCapacityDoesNotAutoAddToCoreWeaveActivePower :
  NamedHostCapacityAutoAddsToCoreWeaveActivePowerPermission → ⊥
namedHostCapacityDoesNotAutoAddToCoreWeaveActivePower ()

facilityDeliveryDoesNotIdentifyGPUGeneration :
  FacilityDeliveryIdentifiesGPUGenerationPermission → ⊥
facilityDeliveryDoesNotIdentifyGPUGeneration ()

boundary : String
boundary =
  "Core Scientific supplies a named, source-paid CoreWeave facility-delivery layer: about 590 MW contracted across five sites, with over 430 MW billing by mid-July 2026 and site-specific delivery schedules. This materially localises part of the infrastructure build. The counterparty 'billing/leased customer power' metric is not definitionally identical to CoreWeave's aggregate active-power metric, so it is not blindly added to the 1.5GW cohort model. The disclosures also do not identify the GPU generation or serial hardware age installed at each named site."
