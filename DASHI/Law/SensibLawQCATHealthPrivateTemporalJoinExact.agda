module DASHI.Law.SensibLawQCATHealthPrivateTemporalJoinExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Law.SensibLawQCATHealthPages82_83PrivateDatasetFixtureExact as Private
import DASHI.Law.SensibLawTemporalHealthEvidenceWrongTypeExact as Temporal

------------------------------------------------------------------------
-- PRIVACY-PRESERVING TEMPORAL JOIN FOR QCAT PP.82-83
--
-- The private workbook holds 89 manually transcribed source rows.  This public
-- fixture exposes only bounded join metadata needed by the legal/evidentiary
-- compiler; it does not republish physiological values or personal notes.
------------------------------------------------------------------------

record PrivateTemporalJoinReceipt : Set₁ where
  constructor privateTemporalJoinReceipt
  field
    privateDatasetDigest : String
    observationWindowReference : String
    sourceRowCountReference : String
    lastPreWindowDisputeEventReference : String
    relationToLastPreWindowEventReference : String
    explicitRussellTextRowCountReference : String
    joinMethodReference : String
    joinReceipt : Set

open PrivateTemporalJoinReceipt public

qcatPages82_83TemporalJoin :
  (joinReceipt : Set) → PrivateTemporalJoinReceipt
qcatPages82_83TemporalJoin joinReceipt =
  privateTemporalJoinReceipt
    Private.privateTranscriptionDigestSha256
    "source observation window 2022-02-23 through 2022-03-03"
    "89 transcribed source rows"
    Temporal.qcat0096Event16Feb
    "all pp.82-83 observations occur after the 2022-02-16 inspection-of-breach event"
    "4 transcribed rows contain explicit Russell text in the source note"
    "raw date/time preserved; no silent date repair; explicit text counted without exposing private measurements"
    joinReceipt

------------------------------------------------------------------------
-- Join authority boundary.
------------------------------------------------------------------------

record PrivateTemporalJoinBoundary : Set where
  constructor privateTemporalJoinBoundary
  field
    afterEventAutomaticallyMeansCausedByEvent : Bool
    afterEventAutomaticallyMeansCausedByEventIsFalse :
      afterEventAutomaticallyMeansCausedByEvent ≡ false

    explicitRussellTextAutomaticallyMeansMedicalCausation : Bool
    explicitRussellTextAutomaticallyMeansMedicalCausationIsFalse :
      explicitRussellTextAutomaticallyMeansMedicalCausation ≡ false

    privateJoinMayRemainDigestAddressed : Bool
    privateJoinMayRemainDigestAddressedIsTrue :
      privateJoinMayRemainDigestAddressed ≡ true

    malformedSourceDateMayBeSilentlyCorrected : Bool
    malformedSourceDateMayBeSilentlyCorrectedIsFalse :
      malformedSourceDateMayBeSilentlyCorrected ≡ false

canonicalPrivateTemporalJoinBoundary : PrivateTemporalJoinBoundary
canonicalPrivateTemporalJoinBoundary =
  privateTemporalJoinBoundary
    false refl
    false refl
    true refl
    false refl
