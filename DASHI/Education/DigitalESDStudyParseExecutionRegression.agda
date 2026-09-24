module DASHI.Education.DigitalESDStudyParseExecutionRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Education.DigitalESDStudyParseExecutionExact as Exec

corpusExecutionMustReconcileCounts :
  Exec.allSourceUnitsParsedExactlyOnce
    Exec.canonicalStudyParseExecutionBoundary
  ≡ true
corpusExecutionMustReconcileCounts = refl

corpusExecutionRemainsCandidateOnly :
  Exec.corpusExecutionCreatesSourceAuditAdmission
    Exec.canonicalStudyParseExecutionBoundary
  ≡ false
corpusExecutionRemainsCandidateOnly = refl

shardReceiptCannotCreateCoordinatePayment :
  Exec.ShardReceiptCreatesExtractionPayment → ⊥
shardReceiptCannotCreateCoordinatePayment =
  Exec.shardReceiptDoesNotCreateExtractionPayment

aggregatePacketCannotCreateAdmission :
  Exec.AggregateParsePacketCreatesSourceAuditAdmission → ⊥
aggregatePacketCannotCreateAdmission =
  Exec.aggregateParsePacketDoesNotCreateSourceAuditAdmission
