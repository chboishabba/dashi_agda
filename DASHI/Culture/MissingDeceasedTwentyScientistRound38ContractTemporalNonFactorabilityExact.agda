module DASHI.Culture.MissingDeceasedTwentyScientistRound38ContractTemporalNonFactorabilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- ROUND 38: CONTRACT-TEMPORAL NON-FACTORABILITY
--
-- Search on FA9300-07-C-0001 exposes a long-lived contract lineage.  A later
-- contract modification or later derivative patent can pay persistence of the
-- contract/object family.  It cannot, by itself, answer whether a particular
-- person held an exact role during the earlier 2011-2013 interval.
--
-- The source role and the DASHI theorem are deliberately separate: the real
-- sources pay later contract persistence; the finite collision below is a
-- repository-local information-theoretic witness and does not assert any
-- undiscovered historical role.
------------------------------------------------------------------------

contractIdentifier : String
contractIdentifier = "FA9300-07-C-0001"

laterModificationSource : Attribution.AttributedSource
laterModificationSource = Attribution.mkNoDOISource
  "United States Department of Defense"
  "Contracts for November 17, 2017 — Aerojet Rocketdyne modification P00139"
  "Department of Defense contract announcement"
  "2017"
  "https://www.war.gov/News/Contracts/Contract/Article/1376191/"
  Attribution.governmentSource
  "Pays later persistence of FA9300-07-C-0001 and a 2017 contract modification; does not identify any retained scientist's 2011-2013 personal role."
  Attribution.publicAttribution

laterPumpPatentSource : Attribution.AttributedSource
laterPumpPatentSource = Attribution.mkNoDOISource
  "United States Patent and Trademark Office; Justia mirror"
  "US11560899 — Pump with axially-elongated annular seal element between inducer and impeller"
  "United States patent record"
  "2023"
  "https://patents.justia.com/patent/11560899"
  Attribution.governmentSource
  "Pays a later technical derivative stating government support under FA9300-07-C-0001; does not identify any retained scientist's 2011-2013 personal role."
  Attribution.publicAttribution

record LaterContractPersistenceReceipt : Set where
  constructor later-contract-persistence-receipt
  field
    source : Attribution.AttributedSource
    sourceDate : String
    exactContractIdentifierPaid : Bool
    laterPersistencePaid : Bool
    earlierPersonalRolePaid : Bool
    whatItPays : String
    whatItDoesNotPay : String

open LaterContractPersistenceReceipt public

modificationPersistenceReceipt : LaterContractPersistenceReceipt
modificationPersistenceReceipt = later-contract-persistence-receipt
  laterModificationSource
  "2017-11-17"
  true
  true
  false
  "later contractual continuity and modification identity for FA9300-07-C-0001"
  "Neil McCasland's, Monica Jacinto's, or any other retained person's exact 2011-2013 task/contract role"

laterPatentPersistenceReceipt : LaterContractPersistenceReceipt
laterPatentPersistenceReceipt = later-contract-persistence-receipt
  laterPumpPatentSource
  "patent filed 2018; issued 2023"
  true
  true
  false
  "later derivative technical lineage explicitly tied to FA9300-07-C-0001"
  "a contemporaneous 2011-2013 personal-role receipt"

round38PersistenceReceipts : List LaterContractPersistenceReceipt
round38PersistenceReceipts = modificationPersistenceReceipt ∷ laterPatentPersistenceReceipt ∷ []

round38PersistenceReceiptCount : Nat
round38PersistenceReceiptCount = 2

data EarlierRoleWorld : Set where
  earlierRolePresent earlierRoleAbsent : EarlierRoleWorld

data LaterPersistenceObservation : Set where
  sameLaterContractPersistence : LaterPersistenceObservation

data EarlierRoleQuery : Set where
  hadEarlierExactRole : EarlierRoleQuery

data EarlierRoleAnswer : Set where
  yesEarlierRole noEarlierRole : EarlierRoleAnswer

projectLaterPersistence : EarlierRoleWorld → LaterPersistenceObservation
projectLaterPersistence _ = sameLaterContractPersistence

answerEarlierRole : EarlierRoleQuery → EarlierRoleWorld → EarlierRoleAnswer
answerEarlierRole hadEarlierExactRole earlierRolePresent = yesEarlierRole
answerEarlierRole hadEarlierExactRole earlierRoleAbsent = noEarlierRole

earlierRoleSemantics : Query.QuerySemantics EarlierRoleWorld EarlierRoleQuery EarlierRoleAnswer
earlierRoleSemantics = Query.querySemantics answerEarlierRole

laterPersistenceQueryDefect :
  Query.QueryAdequacyDefect
    projectLaterPersistence
    earlierRoleSemantics
    hadEarlierExactRole
laterPersistenceQueryDefect =
  Query.queryAdequacyDefect
    earlierRolePresent
    earlierRoleAbsent
    refl
    (λ ())

laterContractPersistenceCannotDetermineEarlierPersonalRole :
  Query.AdequateFor
    projectLaterPersistence
    earlierRoleSemantics
    hadEarlierExactRole →
  ⊥
laterContractPersistenceCannotDetermineEarlierPersonalRole =
  Query.queryAdequacyDefectBlocksFactorisation laterPersistenceQueryDefect

laterDerivativeLineageCannotPayEarlierRole : Bool
laterDerivativeLineageCannotPayEarlierRole = true

laterModificationCannotPayEarlierRole : Bool
laterModificationCannotPayEarlierRole = true

contractIdentityAcrossTimeDoesNotCollapseRoleTime : Bool
contractIdentityAcrossTimeDoesNotCollapseRoleTime = true

syntheticCollisionDoesNotAssertHistoricalRole : Bool
syntheticCollisionDoesNotAssertHistoricalRole = true

contemporaneousIdentityBearingRoleReceiptRepairsDefect : Bool
contemporaneousIdentityBearingRoleReceiptRepairsDefect = true

round38H2PaidCount : Nat
round38H2PaidCount = 0

round38H3PaidCount : Nat
round38H3PaidCount = 0

round38Pareto : String
round38Pareto = "Keep later FA9300-07-C-0001 continuity and derivatives as lineage evidence only. The live H2 debt still requires a contemporaneous 2011-2013 identity-bearing exact-role source: contract modification, programme-review approval chain, attendee/distribution record, materials-task roster, or proceedings paper that literally names the person and role."
