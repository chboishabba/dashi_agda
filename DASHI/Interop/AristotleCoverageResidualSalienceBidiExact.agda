module DASHI.Interop.AristotleCoverageResidualSalienceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ResidualSalienceBidiCrossPollination2026Exact as Salience
import DASHI.Core.ResidualSalienceSchedulerBidiExact as Scheduler
import DASHI.Interop.SensibLawWikidataRequiredPropertyCoverageExact as Coverage
import DASHI.Interop.ZelphPrunedArtifactQueryPreservationExact as Preservation

-- Concrete Nat/Wikimedia residual kinds.
data AristotleCoverageResidual : Set where
  propertyFamilyUninspected
  propertyFamilyIncomplete
  querySoundnessMissing
  queryCompletenessMissing
  revisionAlignmentMissing
  qualifierProfileUninspected
  peerCohortUnresolved : AristotleCoverageResidual

record CoverageResidualSchedulingReceipt : Set where
  constructor coverage-residual-scheduling-receipt
  field
    residualReference : String
    liveHypothesisSetReference : String
    salienceReference : String
    admittedProducerReference : String
    selectedBySalience : Bool
    paidBySelection : Bool
open CoverageResidualSchedulingReceipt public

data SchedulerSelectionImpliesEvidencePayment : Set where
schedulerSelectionDoesNotPayResidual :
  SchedulerSelectionImpliesEvidencePayment → ⊥
schedulerSelectionDoesNotPayResidual ()

data LargestResidualMustBeMostSalient : Set where
largestResidualNeedNotBeMostSalient : LargestResidualMustBeMostSalient → ⊥
largestResidualNeedNotBeMostSalient ()

record AristotleCoverageSalienceBoundary : Set where
  constructor aristotle-coverage-salience-boundary
  field
    salienceDependsOnResidualAndLiveSet : Bool
    smallCoverageResidualMayDominate : Bool
    magnitudeDeterminesSalience : Bool
    schedulerSelectionCreatesEvidence : Bool

canonicalAristotleCoverageSalienceBoundary : AristotleCoverageSalienceBoundary
canonicalAristotleCoverageSalienceBoundary =
  aristotle-coverage-salience-boundary true true false false

coverageSalienceStatement : String
coverageSalienceStatement =
  "Nat/Wikimedia coverage residuals can be scheduled by consumer-separating salience. A single missing Q/P family or preservation receipt may dominate many low-value observations when it blocks all surviving hypotheses, but salience does not manufacture admission and scheduler selection does not pay the evidence obligation."
