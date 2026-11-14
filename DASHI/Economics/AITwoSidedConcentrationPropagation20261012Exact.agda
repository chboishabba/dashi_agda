module DASHI.Economics.AITwoSidedConcentrationPropagation20261012Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- TWO-SIDED CONCENTRATION AROUND COREWEAVE
--
-- Downstream: CoreWeave Q2-2026 top-three customers = 36%, 26%, 10%.
-- Upstream: Core Scientific H1-2026 says CoreWeave = ~77% of total revenue.
-- This is a concentration-propagation topology, not a default-correlation or
-- terminal-payer theorem.
------------------------------------------------------------------------

secFilingKind : Source.SourceKind
secFilingKind = Source.namedSourceKind "primary SEC filing"

coreWeaveQ22026Source : Source.AttributedSource
coreWeaveQ22026Source = Source.mkNoDOISource
  "CoreWeave, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm"
  secFilingKind
  "primary carrier for Q2-2026 top-three customer revenue shares 36 percent, 26 percent and 10 percent"
  Source.publicAttribution

coreScientificQ22026Source : Source.AttributedSource
coreScientificQ22026Source = Source.mkNoDOISource
  "Core Scientific, Inc."
  "Quarterly report for period ended June 30 2026"
  "SEC Form 10-Q"
  "2026"
  "https://www.sec.gov/Archives/edgar/data/1839341/000183934126000014/core-20260630.htm"
  secFilingKind
  "primary carrier for CoreWeave representing approximately 77 percent of Core Scientific total H1-2026 revenue and all current colocation revenue"
  Source.publicAttribution

record DownstreamConcentrationBounds : Set where
  constructor downstreamConcentrationBounds
  field
    knownRevenueShareBp : Nat
    hhiLowerBp : Nat
    hhiUpperBp : Nat
    source : Source.AttributedSource

open DownstreamConcentrationBounds public

coreWeaveDownstreamBounds : DownstreamConcentrationBounds
coreWeaveDownstreamBounds = downstreamConcentrationBounds 7200 2072 2856 coreWeaveQ22026Source

record UpstreamDependencyPoint : Set where
  constructor upstreamDependencyPoint
  field
    provider : String
    platform : String
    platformRevenueShareBp : Nat
    source : Source.AttributedSource

open UpstreamDependencyPoint public

coreScientificCoreWeaveDependency : UpstreamDependencyPoint
coreScientificCoreWeaveDependency = upstreamDependencyPoint
  "Core Scientific" "CoreWeave" 7700 coreScientificQ22026Source

record TwoSidedConcentrationObservation : Set where
  constructor twoSidedConcentrationObservation
  field
    downstream : DownstreamConcentrationBounds
    upstream : UpstreamDependencyPoint
    twoSidedConcentrationObserved : Bool
    terminalPayerIndependenceClosed : Bool
    defaultCorrelationMagnitudeClosed : Bool
    systemicFailureProbabilityClosed : Bool

open TwoSidedConcentrationObservation public

coreWeaveTwoSidedConcentration : TwoSidedConcentrationObservation
coreWeaveTwoSidedConcentration = twoSidedConcentrationObservation
  coreWeaveDownstreamBounds coreScientificCoreWeaveDependency
  true false false false

------------------------------------------------------------------------
-- Non-promotion firewalls.
------------------------------------------------------------------------

data TwoSidedConcentrationImpliesTerminalDependencePermission : Set where
data TwoSidedConcentrationImpliesDefaultCorrelationPermission : Set where
data TwoSidedConcentrationImpliesSystemicFailurePermission : Set where

twoSidedConcentrationDoesNotAutoCloseTerminalDependence :
  TwoSidedConcentrationImpliesTerminalDependencePermission → ⊥
twoSidedConcentrationDoesNotAutoCloseTerminalDependence ()

twoSidedConcentrationDoesNotAutoCreateDefaultCorrelation :
  TwoSidedConcentrationImpliesDefaultCorrelationPermission → ⊥
twoSidedConcentrationDoesNotAutoCreateDefaultCorrelation ()

twoSidedConcentrationDoesNotAutoCreateSystemicFailure :
  TwoSidedConcentrationImpliesSystemicFailurePermission → ⊥
twoSidedConcentrationDoesNotAutoCreateSystemicFailure ()

coreWeaveKnownShareIs7200bp : knownRevenueShareBp coreWeaveDownstreamBounds ≡ 7200
coreWeaveKnownShareIs7200bp = refl

coreWeaveHHILowerIs2072bp : hhiLowerBp coreWeaveDownstreamBounds ≡ 2072
coreWeaveHHILowerIs2072bp = refl

coreScientificDependencyIs7700bp : platformRevenueShareBp coreScientificCoreWeaveDependency ≡ 7700
coreScientificDependencyIs7700bp = refl

terminalIndependenceStillOpen : terminalPayerIndependenceClosed coreWeaveTwoSidedConcentration ≡ false
terminalIndependenceStillOpen = refl
