module DASHI.Governance.IRISDenaIranContraOpacityNonanalogyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Governance.IranContraCovertFlowHistoricalMechanismExact as IranContra
import DASHI.Governance.IRISDenaPublicRecordCeilingAndFOIExact as IRIS

------------------------------------------------------------------------
-- IRAN/CONTRA POSITIVE DIVERGENCE WITNESS vs IRIS-DENA OPACITY
------------------------------------------------------------------------

data OperationalKnowledgeState : Set where
  documentedPolicyOperationalDivergence : OperationalKnowledgeState
  publicRecordIncomplete : OperationalKnowledgeState
  exactOperationalRecordPaid : OperationalKnowledgeState

record HistoricalPositiveWitness : Set where
  constructor historical-positive-witness
  field
    state : OperationalKnowledgeState
    sourceRef : String
    divergencePaid : Bool
    divergencePaidIsTrue : divergencePaid ≡ true
    offBooksRoutingPaid : Bool
    offBooksRoutingPaidIsTrue : offBooksRoutingPaid ≡ true

open HistoricalPositiveWitness public

iranContraPositiveWitness : HistoricalPositiveWitness
iranContraPositiveWitness =
  historical-positive-witness
    documentedPolicyOperationalDivergence
    "IranContraCovertFlowHistoricalMechanismExact.iranContraTopology"
    true refl
    true refl

record CurrentOpacityWitness : Set where
  constructor current-opacity-witness
  field
    state : OperationalKnowledgeState
    ceiling : IRIS.PublicRecordCeiling
    missingObjectRef : String
    publicRecordIncompletePaid : Bool
    publicRecordIncompletePaidIsTrue :
      publicRecordIncompletePaid ≡ true
    policyOperationalDivergencePaid : Bool
    policyOperationalDivergencePaidIsFalse :
      policyOperationalDivergencePaid ≡ false
    covertRoutingPaid : Bool
    covertRoutingPaidIsFalse :
      covertRoutingPaid ≡ false

open CurrentOpacityWitness public

irisOpacityWitness : CurrentOpacityWitness
irisOpacityWitness =
  current-opacity-witness
    publicRecordIncomplete
    IRIS.canonicalPublicRecordCeiling
    "proof Hansard / watchbill / embedding protocol / action log"
    true refl
    false refl
    false refl

data OperationalOpacityMeansCovertDivergence : Set where
data MissingProtocolMeansSecretIllegalProtocol : Set where
data HistoricalAnalogyFillsCurrentRecordGap : Set where
data CurrentGovernmentStatementClosesOperationalRecord : Set where

opacityDoesNotCreateCovertDivergence :
  OperationalOpacityMeansCovertDivergence → ⊥
opacityDoesNotCreateCovertDivergence ()

missingProtocolDoesNotCreateIllegality :
  MissingProtocolMeansSecretIllegalProtocol → ⊥
missingProtocolDoesNotCreateIllegality ()

historicalAnalogyDoesNotFillRecordGap :
  HistoricalAnalogyFillsCurrentRecordGap → ⊥
historicalAnalogyDoesNotFillRecordGap ()

governmentStatementDoesNotCloseOperationalRecord :
  CurrentGovernmentStatementClosesOperationalRecord → ⊥
governmentStatementDoesNotCloseOperationalRecord ()

historicalReference :
  IranContra.HistoricalRoutingTopology
historicalReference = IranContra.iranContraTopology
