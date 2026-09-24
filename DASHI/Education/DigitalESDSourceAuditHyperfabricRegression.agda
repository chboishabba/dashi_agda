module DASHI.Education.DigitalESDSourceAuditHyperfabricRegression where

open import DASHI.Core.Prelude
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDSourceAuditHyperfabricExact as Hyperfabric

coarseCannotRecoverFullAudit :
  Hyperfabric.CoarseVisibilityProfileDeterminesFullAuditState → ⊥
coarseCannotRecoverFullAudit =
  Hyperfabric.coarseVisibilityProfileDoesNotDetermineFullAuditState

scoreNotEvidence : Hyperfabric.ScoreProfileCreatesEvidenceObject → ⊥
scoreNotEvidence = Hyperfabric.scoreProfileDoesNotCreateEvidenceObject

singleObserverNotWhole : Hyperfabric.SingleObserverCreatesWholeAuditState → ⊥
singleObserverNotWhole = Hyperfabric.singleObserverDoesNotCreateWholeAuditState
