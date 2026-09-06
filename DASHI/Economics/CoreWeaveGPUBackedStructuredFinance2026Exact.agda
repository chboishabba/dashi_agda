module DASHI.Economics.CoreWeaveGPUBackedStructuredFinance2026Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Economics.AIStructuredInfrastructureCommonFactorRiskExact as AI
import DASHI.Economics.CommonFactorStructuredFinanceExact as Structured

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    date : String
    sourceLocation : String
    boundedProposition : String
    primarySource : Bool

open SourceReceipt public

investmentGradeGPUBackedFacility : SourceReceipt
investmentGradeGPUBackedFacility = sourceReceipt
  "2026-03-31"
  "CoreWeave investor relations"
  "CoreWeave closed an USD 8.5 billion non-recourse delayed-draw term loan facility rated A3/A(low), secured by HPC infrastructure and an associated customer contract."
  true

publiclySyndicatedFacility : SourceReceipt
publiclySyndicatedFacility = sourceReceipt
  "2026-05-18"
  "CoreWeave SEC exhibit / investor release"
  "CoreWeave closed a USD 3.1 billion publicly syndicated HPC-backed delayed-draw term loan supporting infrastructure dedicated to two customer contracts and enabling secondary-market trading."
  true

maturityContractMismatch : SourceReceipt
maturityContractMismatch = sourceReceipt
  "2026-08-10"
  "CoreWeave investor relations"
  "CoreWeave closed a USD 2.6 billion facility with an approximate five-year maturity extending beyond the average three-year length of underlying customer contracts."
  true

record CoreWeaveStructuredFinanceCalibration : Set where
  constructor coreWeaveStructuredFinanceCalibration
  field
    investmentGradeReceipt : SourceReceipt
    syndicatedReceipt : SourceReceipt
    maturityReceipt : SourceReceipt
    infrastructureAndContractBackFinancing : Bool
    publiclySyndicatedSecondaryMarketInstrument : Bool
    debtMaturityExceedsAverageUnderlyingContractTerm : Bool
    classicalCDOProven : Bool
    resecuritisationProven : Bool
    ultimateRiskFactorIndependenceProven : Bool

canonicalCoreWeaveStructuredFinanceCalibration :
  CoreWeaveStructuredFinanceCalibration
canonicalCoreWeaveStructuredFinanceCalibration =
  coreWeaveStructuredFinanceCalibration
    investmentGradeGPUBackedFacility
    publiclySyndicatedFacility
    maturityContractMismatch
    true true true false false false

projectMultiplicityDoesNotCloseIndependence :
  Structured.ProjectMultiplicityImpliesRiskIndependencePermission → ⊥
projectMultiplicityDoesNotCloseIndependence =
  AI.projectMultiplicityDoesNotCloseRiskIndependence

data GPUBackedFacilityEqualsClassicalCDOPermission : Set where

gpuBackedFacilityDoesNotAutoPromoteToClassicalCDO :
  GPUBackedFacilityEqualsClassicalCDOPermission → ⊥
gpuBackedFacilityDoesNotAutoPromoteToClassicalCDO ()
