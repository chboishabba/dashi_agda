module DASHI.Cognition.PNF.NarrativeMDLReplicationExact where

------------------------------------------------------------------------
-- NARRATIVE DESCRIPTION-LENGTH / REPLICATION ASYMMETRY
--
-- Mathematical reference:
--   Jorma Rissanen,
--   "Modeling by shortest data description",
--   Automatica 14(5) (1978), 465-471.
--   DOI: 10.1016/0005-1098(78)90005-5
--
-- This finite module does NOT claim that shortest rhetoric is truest.  It only
-- formalizes the transmission asymmetry identified in the supplied beef
-- analysis: a compact classifier may fit a bounded broadcast budget while a
-- longer corrective/reopening explanation does not.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)

import DASHI.Core.ApproximateMDLResidualBudgetExact as MDL

------------------------------------------------------------------------
-- Concrete toy code lengths.  The value 3 records the three-word title
-- "Not Like Us" only as a finite encoding example; it is not a statistical
-- estimate of real-world semantic complexity.
------------------------------------------------------------------------

anthemCodeLength : Nat
anthemCodeLength = 3

minimalReopeningCodeLength : Nat
minimalReopeningCodeLength = 4

broadcastBudget : Nat
broadcastBudget = 3

anthemFitsBroadcastBudget :
  MDL.WithinResidualBudget anthemCodeLength broadcastBudget
anthemFitsBroadcastBudget =
  MDL.withinResidualBudget zero refl

reopeningDoesNotFitSameBudget :
  MDL.WithinResidualBudget minimalReopeningCodeLength broadcastBudget → ⊥
reopeningDoesNotFitSameBudget (MDL.withinResidualBudget slack ())

------------------------------------------------------------------------
-- Description length and truth are independent axes.
------------------------------------------------------------------------

data TruthCoordinate : Set where
  supported refuted unresolved : TruthCoordinate

data CompressionWinner : Set where
  shorter longer tie : CompressionWinner

data CompressionSettlesTruth : CompressionWinner → TruthCoordinate → Set where

shorterDoesNotProveSupported :
  CompressionSettlesTruth shorter supported → ⊥
shorterDoesNotProveSupported ()

shorterDoesNotProveRefuted :
  CompressionSettlesTruth shorter refuted → ⊥
shorterDoesNotProveRefuted ()

------------------------------------------------------------------------
-- A compact classifier may therefore dominate one finite transmission channel
-- while factual adjudication remains explicitly unresolved.
------------------------------------------------------------------------

record TransmissionState : Set where
  constructor transmissionState
  field
    compression : CompressionWinner
    truth : TruthCoordinate

open TransmissionState public

compactButUnresolved : TransmissionState
compactButUnresolved = transmissionState shorter unresolved

compactnessLeavesTruthUnresolved :
  truth compactButUnresolved ≡ unresolved
compactnessLeavesTruthUnresolved = refl
