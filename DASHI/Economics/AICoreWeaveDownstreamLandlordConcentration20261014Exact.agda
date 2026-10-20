module DASHI.Economics.AICoreWeaveDownstreamLandlordConcentration20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

primarySECQuarterlyFiling : Source.SourceKind
primarySECQuarterlyFiling = Source.namedSourceKind "primary SEC quarterly filing"

coreScientificQ22026Source : Source.AttributedSource
coreScientificQ22026Source = Source.mkNoDOISource
  "Core Scientific, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026-08"
  "https://www.sec.gov/Archives/edgar/data/1839341/000183934126000052/corz-20260630.htm"
  primarySECQuarterlyFiling
  "reports CoreWeave represented approximately 77 percent of revenue for the quarter; approximately 590 MW contracted and 395 MW billing under CoreWeave agreements; certain licenses were assigned to a CoreWeave special-purpose vehicle while CoreWeave remained primary obligor"
  Source.publicAttribution

record DownstreamLandlordConcentration : Set where
  constructor downstream-landlord-concentration
  field
    payer : String
    operator : String
    revenueShareBp : Nat
    contractedMW : Nat
    billingMW : Nat
    spvAssignment : Bool
    payerRemainsPrimaryObligor : Bool
    terminalCashIndependencePaid : Bool
    circularCashEstablished : Bool
    systemicFailureEstablished : Bool

open DownstreamLandlordConcentration public

coreScientificCoreWeaveConcentration : DownstreamLandlordConcentration
coreScientificCoreWeaveConcentration = downstream-landlord-concentration
  "CoreWeave" "Core Scientific" 7700 590 395 true true false false false

coreWeaveRevenueShareBpIs7700 :
  revenueShareBp coreScientificCoreWeaveConcentration ≡ 7700
coreWeaveRevenueShareBpIs7700 = refl

contractedMWIs590 : contractedMW coreScientificCoreWeaveConcentration ≡ 590
contractedMWIs590 = refl

billingMWIs395 : billingMW coreScientificCoreWeaveConcentration ≡ 395
billingMWIs395 = refl

spvAssignmentObserved : spvAssignment coreScientificCoreWeaveConcentration ≡ true
spvAssignmentObserved = refl

coreWeavePrimaryObligorObserved :
  payerRemainsPrimaryObligor coreScientificCoreWeaveConcentration ≡ true
coreWeavePrimaryObligorObserved = refl

data DownstreamConcentrationImpliesCircularCashPermission : Set where
data SPVAssignmentImpliesObligorReleasePermission : Set where
data ConcentrationImpliesSystemicFailurePermission : Set where

downstreamConcentrationDoesNotCreateCircularCash :
  DownstreamConcentrationImpliesCircularCashPermission → ⊥
downstreamConcentrationDoesNotCreateCircularCash ()

spvAssignmentDoesNotReleasePrimaryObligor :
  SPVAssignmentImpliesObligorReleasePermission → ⊥
spvAssignmentDoesNotReleasePrimaryObligor ()

concentrationDoesNotCreateSystemicFailure :
  ConcentrationImpliesSystemicFailurePermission → ⊥
concentrationDoesNotCreateSystemicFailure ()

boundary : String
boundary =
  "Core Scientific's Q2-2026 SEC filing pays a downstream concentration edge: CoreWeave is approximately 77 percent of quarterly revenue, with about 590 MW contracted and 395 MW billing; some licenses were assigned to a CoreWeave SPV while CoreWeave remained primary obligor. This demonstrates material dependency and SPV topology, not circular cash, terminal-cash independence, obligor release, or systemic failure."
