module DASHI.Governance.AUKUSPersonnelExchangeMOUExistenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- AUKUS PERSONNEL-EXCHANGE MOU: EXISTENCE vs OPERATIVE CONTENT
--
-- Official Australian/U.S./trilateral material pays existence and purpose of
-- bilateral personnel-exchange MOUs.  It does not publish the operative
-- clauses governing an embedded sailor during third-party hostilities.
------------------------------------------------------------------------

defenceMinistersJointStatement2024 : Source.AttributedSource
defenceMinistersJointStatement2024 = Source.mkNoDOISource
  "AUKUS Defence Ministers"
  "AUKUS Defence Ministers' Joint Statement"
  "Australian Department of Defence / Defence Ministers"
  "2024-04-09"
  "https://www.minister.defence.gov.au/statements/2024-04-09/aukus-defence-ministers-joint-statement"
  Source.governmentSource
  "primary official statement: Australia-US and Australia-UK bilateral MOUs for personnel exchanges had been signed to accelerate sovereign-workforce growth; operative command/direction clauses are not reproduced"
  Source.publicAttribution

asaAnnualReport2024 : Source.AttributedSource
asaAnnualReport2024 = Source.mkNoDOISource
  "Australian Submarine Agency"
  "Annual Report 2023-24"
  "Australian Submarine Agency"
  "2024"
  "https://www.asa.gov.au/sites/default/files/documents/2024-10/ASA_Annual_Report_2023-24.pdf"
  Source.governmentSource
  "primary agency report: target to establish personnel exchange agreements with the UK and US for APS/ADF personnel was achieved; cites the April 2024 ministerial statement"
  Source.publicAttribution

record MOUExistenceReceipt : Set where
  constructor mou-existence-receipt
  field
    source : Source.AttributedSource
    bilateralAustraliaUSMOUExists : Bool
    bilateralAustraliaUSMOUExistsIsTrue :
      bilateralAustraliaUSMOUExists ≡ true
    personnelExchangePurposePaid : Bool
    personnelExchangePurposePaidIsTrue :
      personnelExchangePurposePaid ≡ true
    operativeDirectionClausesPublished : Bool
    operativeDirectionClausesPublishedIsFalse :
      operativeDirectionClausesPublished ≡ false
    thirdPartyHostilityRulesPublished : Bool
    thirdPartyHostilityRulesPublishedIsFalse :
      thirdPartyHostilityRulesPublished ≡ false
    exactIRISEpisodeTaskPaid : Bool
    exactIRISEpisodeTaskPaidIsFalse :
      exactIRISEpisodeTaskPaid ≡ false

open MOUExistenceReceipt public

canonicalMOUExistence : MOUExistenceReceipt
canonicalMOUExistence =
  mou-existence-receipt
    defenceMinistersJointStatement2024
    true refl
    true refl
    false refl
    false refl
    false refl

record RemainingMOUResidual : Set where
  constructor remaining-mou-residual
  field
    residualRef : String
    alreadyPaid : String
    requiredObject : String
    existenceMustNotBeReacquired : Bool
    existenceMustNotBeReacquiredIsTrue :
      existenceMustNotBeReacquired ≡ true

open RemainingMOUResidual public

operativeMOUResidual : RemainingMOUResidual
operativeMOUResidual =
  remaining-mou-residual
    "residual:aukus:personnel-exchange-mou-operative-content"
    "primary official existence + personnel-exchange purpose"
    "actual Australia-US personnel-exchange MOU text and operative annexes/clauses relevant to direction authority, command and third-party hostilities"
    true refl

data MOUExistenceMeansOperativeTermsKnown : Set where
data WorkforcePurposeMeansCombatAuthorityKnown : Set where
data OfficialMOUExistenceMeansMarch2026TaskKnown : Set where

existenceDoesNotRevealOperativeTerms :
  MOUExistenceMeansOperativeTermsKnown → ⊥
existenceDoesNotRevealOperativeTerms ()

workforcePurposeDoesNotRevealCombatAuthority :
  WorkforcePurposeMeansCombatAuthorityKnown → ⊥
workforcePurposeDoesNotRevealCombatAuthority ()

mouExistenceDoesNotRevealIRISTask :
  OfficialMOUExistenceMeansMarch2026TaskKnown → ⊥
mouExistenceDoesNotRevealIRISTask ()

ministerialSnowball :
  Snowball.SourceRoleSnowballReceipt defenceMinistersJointStatement2024
ministerialSnowball =
  Snowball.canonicalSourceRoleSnowballReceipt defenceMinistersJointStatement2024

asaSnowball : Snowball.SourceRoleSnowballReceipt asaAnnualReport2024
asaSnowball = Snowball.canonicalSourceRoleSnowballReceipt asaAnnualReport2024
