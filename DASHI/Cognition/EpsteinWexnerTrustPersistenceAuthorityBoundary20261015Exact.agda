module DASHI.Cognition.EpsteinWexnerTrustPersistenceAuthorityBoundary20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinWexnerTrusteeTenureBoundary20261015Exact as Tenure

------------------------------------------------------------------------
-- TRUST PERSISTENCE != TRUSTEE PERSISTENCE
--
-- Later SEC filings establish that Wexner Children's Trust II continued to
-- exist and transact after the Epstein/Wexner relationship period.  Those later
-- filings identify Wexner-family beneficial-ownership reporting but do not name
-- Epstein as trustee.  Entity persistence cannot extend an earlier trustee
-- tenure without a trustee certificate/amendment/successor instrument.
------------------------------------------------------------------------

data PersistenceSource : Set where
  secForm4 : PersistenceSource
  secSchedule13D : PersistenceSource

record TrustPersistenceReceipt : Set where
  constructor trust-persistence-receipt
  field
    date : String
    source : String
    sourceClass : PersistenceSource
    boundedFinding : String
    trustEntityActivePaid : Bool
    epsteinTrusteeAtDatePaid : Bool
open TrustPersistenceReceipt public

trustActivity2010 : TrustPersistenceReceipt
trustActivity2010 = trust-persistence-receipt
  "2010-09-08"
  "SEC Form 4, accession 0001140361-10-036556"
  secForm4
  "The filing reports Leslie Wexner transferring 2,478,115 Limited Brands shares to Wexner Children's Trust II on 9 June 2010 and the trust selling 2,000,000 shares on 8 September 2010 at USD25.37, leaving 478,115 shares. The reporting-person signatures are Leslie/Abigail Wexner; this filing establishes trust activity but does not identify Epstein as trustee."
  true false

trustActivity202103 : TrustPersistenceReceipt
trustActivity202103 = trust-persistence-receipt
  "2021-03-24"
  "SEC Form 4, accession 0001140361-21-009790"
  secForm4
  "The filing reports a March 2021 transfer of 2,000,000 L Brands shares to Wexner Children's Trust II followed by sale at USD58.31. It treats the trust as indirect ownership in Wexner-family reporting and contains no Epstein trustee signature."
  true false

trustActivity202106 : TrustPersistenceReceipt
trustActivity202106 = trust-persistence-receipt
  "2021-06-07"
  "SEC Form 4, accession 0001140361-21-020078"
  secForm4
  "The filing reports a June 2021 gift of 3,500,000 shares to Wexner Children's Trust II and sale at USD65.30. Again, trust persistence/activity is paid while Epstein trustee status at that date is not."
  true false

record PersistenceBoundary : Set where
  constructor persistence-boundary
  field
    trustPersistsInto2010Paid : Bool
    trustPersistsInto2021Paid : Bool
    laterSECActivityNamesEpsteinTrustee : Bool
    entityPersistenceImpliesSameTrustee : Bool
    lackOfEpsteinSignatureProvesExactRemovalDate : Bool
    successorInstrumentStillRequired : Bool
open PersistenceBoundary public

canonicalPersistenceBoundary : PersistenceBoundary
canonicalPersistenceBoundary = persistence-boundary
  true true false false false true

data EntityPersistenceImpliesTrusteePersistence : Set where
data MissingSignatureProvesRemoval : Set where

entityPersistenceDoesNotCreateTrusteePersistence : EntityPersistenceImpliesTrusteePersistence → ⊥
entityPersistenceDoesNotCreateTrusteePersistence ()

missingSignatureDoesNotCreateRemovalDate : MissingSignatureProvesRemoval → ⊥
missingSignatureDoesNotCreateRemovalDate ()

------------------------------------------------------------------------
-- Acquisition target remains the transition instrument, not later trust acts.
------------------------------------------------------------------------

data PersistenceDebt : Set where
  lastNeutralEpsteinTrusteeRecord : PersistenceDebt
  firstNeutralSuccessorTrusteeRecord : PersistenceDebt
  removalOrResignationInstrument : PersistenceDebt
  amendmentRestatementChain : PersistenceDebt

record PersistenceAcquisition : Set where
  constructor persistence-acquisition
  field
    debt : PersistenceDebt
    priority : Nat
    question : String
open PersistenceAcquisition public

canonicalPersistenceAcquisition : List PersistenceAcquisition
canonicalPersistenceAcquisition =
  persistence-acquisition removalOrResignationInstrument 100
    "Acquire Epstein's trustee resignation/removal or successor appointment; later trust activity is not a substitute for the transition instrument." ∷
  persistence-acquisition firstNeutralSuccessorTrusteeRecord 100
    "Find the earliest neutral bank/SEC/trust record naming the successor trustee to narrow the upper endpoint of Epstein's tenure." ∷
  persistence-acquisition lastNeutralEpsteinTrusteeRecord 99
    "Find the latest neutral signature/certificate naming Epstein trustee, currently later than creation but earlier than the 2006/07 pleading assertions." ∷
  persistence-acquisition amendmentRestatementChain 99
    "Recover amendments/restatements linking the 1998 instrument to the later active trust identity." ∷
  []
