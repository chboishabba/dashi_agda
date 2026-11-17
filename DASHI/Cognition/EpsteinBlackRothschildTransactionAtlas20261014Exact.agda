module DASHI.Cognition.EpsteinBlackRothschildTransactionAtlas20261014Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- EFTA00027019 / DB-SDNY SAME-OBJECT TRANSACTION ATLAS
--
-- This owner records literal payer -> recipient -> amount edges from the DOJ
-- exhibit.  A wire does not import its economic purpose, knowledge, wrongdoing,
-- control, shared operation or relationship beyond the payment itself.
------------------------------------------------------------------------

data TransactionParty : Set where
  leonAndDebraBlack : TransactionParty
  blackFamilyPartners : TransactionParty
  narrowHoldings : TransactionParty
  bv70 : TransactionParty
  edmondDeRothschildSuisse : TransactionParty
  benjaminEdmondDeRothschild : TransactionParty
  southernTrust : TransactionParty
  gratitudeAmerica : TransactionParty
  planD : TransactionParty

record TransactionReceipt : Set where
  constructor transaction-receipt
  field
    date : String
    payer : TransactionParty
    recipient : TransactionParty
    amountUSD : Nat
    bates : String
    payerLabel : String
    boundedFinding : String
    paymentPaid : Bool
    purposePaid : Bool
    wrongdoingPaid : Bool
open TransactionReceipt public

black20131015 : TransactionReceipt
black20131015 = transaction-receipt "2013-10-15" leonAndDebraBlack southernTrust 8500000 "DB-SDNY-0002962"
  "Leon and Debra Black" "DOJ exhibit records USD 8.5m to Southern Trust Company." true false false

blackFamily20131218 : TransactionReceipt
blackFamily20131218 = transaction-receipt "2013-12-18" blackFamilyPartners southernTrust 10000000 "DB-SDNY-0003484"
  "Black Family Partners LP c/o Apollo Management" "DOJ exhibit records USD 10m to Southern Trust Company; the c/o address is an administrative locator and does not make Apollo the payer." true false false

black20140425 : TransactionReceipt
black20140425 = transaction-receipt "2014-04-25" leonAndDebraBlack southernTrust 5000000 "DB-SDNY-0003819"
  "Leon and Debra Black" "DOJ exhibit records USD 5m to Southern Trust Company." true false false

blackFamily20140425 : TransactionReceipt
blackFamily20140425 = transaction-receipt "2014-04-25" blackFamilyPartners southernTrust 5000000 "DB-SDNY-0003819"
  "Black Family Partners LP c/o Apollo Management" "DOJ exhibit records USD 5m to Southern Trust Company." true false false

black20140429 : TransactionReceipt
black20140429 = transaction-receipt "2014-04-29" leonAndDebraBlack southernTrust 15000000 "DB-SDNY-0003819"
  "Leon and Debra Black" "DOJ exhibit records USD 15m to Southern Trust Company." true false false

narrow20140715 : TransactionReceipt
narrow20140715 = transaction-receipt "2014-07-15" narrowHoldings southernTrust 20000000 "DB-SDNY-0004009"
  "Narrow Holdings LLC c/o Elysium Management" "DOJ exhibit records USD 20m to Southern Trust Company." true false false

black20141016 : TransactionReceipt
black20141016 = transaction-receipt "2014-10-16" leonAndDebraBlack southernTrust 7000000 "DB-SDNY-0004172"
  "Leon and Debra Black" "DOJ exhibit records USD 7m to Southern Trust Company." true false false

blackFamily20141016 : TransactionReceipt
blackFamily20141016 = transaction-receipt "2014-10-16" blackFamilyPartners southernTrust 13000000 "DB-SDNY-0004172"
  "Black Family Partners LP c/o Apollo Management" "DOJ exhibit records USD 13m to Southern Trust Company." true false false

black20141022 : TransactionReceipt
black20141022 = transaction-receipt "2014-10-22" leonAndDebraBlack southernTrust 2000000 "DB-SDNY-0004173"
  "Leon and Debra Black c/o Apollo Management" "DOJ exhibit records USD 2m to Southern Trust Company." true false false

blackFamily20141022 : TransactionReceipt
blackFamily20141022 = transaction-receipt "2014-10-22" blackFamilyPartners southernTrust 3000000 "DB-SDNY-0004173"
  "Black Family Partners LP c/o Apollo Management" "DOJ exhibit records USD 3m to Southern Trust Company." true false false

black20151013 : TransactionReceipt
black20151013 = transaction-receipt "2015-10-13" leonAndDebraBlack southernTrust 5000000 "DB-SDNY-0004990"
  "Leon and Debra Black c/o Apollo Management" "DOJ exhibit records USD 5m to Southern Trust Company." true false false

blackFamily20151013 : TransactionReceipt
blackFamily20151013 = transaction-receipt "2015-10-13" blackFamilyPartners southernTrust 5000000 "DB-SDNY-0004990"
  "Black Family Partners LP c/o Apollo Management" "DOJ exhibit records USD 5m to Southern Trust Company." true false false

bv70Gratitude20151014 : TransactionReceipt
bv70Gratitude20151014 = transaction-receipt "2015-10-14" bv70 gratitudeAmerica 10000000 "DB-SDNY-0004999"
  "BV70 LLC" "DOJ exhibit records USD 10m to Epstein-affiliated Gratitude America." true false false

rothschildBank20151217 : TransactionReceipt
rothschildBank20151217 = transaction-receipt "2015-12-17" edmondDeRothschildSuisse southernTrust 10000000 "DB-SDNY-0005122"
  "Edmond de Rothschild (Suisse) SA, Geneva" "DOJ exhibit records USD 10m to Southern Trust Company. The exhibit pays the transfer, not its purpose or any wrongdoing inference." true false false

blackFamily20151218 : TransactionReceipt
blackFamily20151218 = transaction-receipt "2015-12-18" blackFamilyPartners southernTrust 10000000 "DB-SDNY-0005122"
  "Black Family Partners LP" "DOJ exhibit records USD 10m to Southern Trust Company." true false false

benjaminRothschild20151221 : TransactionReceipt
benjaminRothschild20151221 = transaction-receipt "2015-12-21" benjaminEdmondDeRothschild southernTrust 14999980 "DB-SDNY-0005122"
  "Benjamin Edmond de Rothschild" "DOJ exhibit records USD 14,999,980 to Southern Trust Company. Purpose remains unresolved in this owner." true false false

black20151230 : TransactionReceipt
black20151230 = transaction-receipt "2015-12-30" leonAndDebraBlack southernTrust 10000000 "DB-SDNY-0005123"
  "Leon and Debra Black c/o Apollo Management" "DOJ exhibit records USD 10m to Southern Trust Company." true false false

bv70Loan20170331 : TransactionReceipt
bv70Loan20170331 = transaction-receipt "2017-03-31" bv70 planD 22500000 "DB-SDNY-0006113"
  "BV70 LLC" "DOJ exhibit records USD 22.5m to Epstein-owned Plan D LLC; Dechert classifies this as a documented loan connected to an art transaction." true true false

bv70Loan20170417 : TransactionReceipt
bv70Loan20170417 = transaction-receipt "2017-04-17" bv70 planD 8000000 "DB-SDNY-0006197"
  "BV70 LLC" "DOJ exhibit records USD 8m to Plan D LLC; Dechert classifies this as the second documented loan." true true false

black20170425 : TransactionReceipt
black20170425 = transaction-receipt "2017-04-25" leonAndDebraBlack southernTrust 8000000 "DB-SDNY-0006240"
  "Leon and Debra Black c/o Apollo Management" "DOJ exhibit records USD 8m to Southern Trust Company; Dechert attributes the final 2017 payment to tax advisory/compliance services." true true false

allLocatedTransactions : List TransactionReceipt
allLocatedTransactions =
  black20131015 ∷ blackFamily20131218 ∷ black20140425 ∷ blackFamily20140425 ∷
  black20140429 ∷ narrow20140715 ∷ black20141016 ∷ blackFamily20141016 ∷
  black20141022 ∷ blackFamily20141022 ∷ black20151013 ∷ blackFamily20151013 ∷
  bv70Gratitude20151014 ∷ rothschildBank20151217 ∷ blackFamily20151218 ∷
  benjaminRothschild20151221 ∷ black20151230 ∷ bv70Loan20170331 ∷
  bv70Loan20170417 ∷ black20170425 ∷ []

record RothschildBoundary : Set where
  constructor rothschild-boundary
  field
    institutionalWirePaid : Bool
    personalWirePaid : Bool
    combinedLocatedAmountUSD : Nat
    purposePaid : Bool
    paymentImpliesCommonOperation : Bool
    surnameImpliesFamilyWideAgency : Bool
open RothschildBoundary public

canonicalRothschildBoundary : RothschildBoundary
canonicalRothschildBoundary = rothschild-boundary true true 24999980 false false false

data WireImpliesIllicitPurpose : Set where
data WireImpliesCommonOperation : Set where
data RothschildWireImpliesFamilyWideAgency : Set where
data CareOfApolloImpliesApolloPayer : Set where

wireDoesNotCreateIllicitPurpose : WireImpliesIllicitPurpose → ⊥
wireDoesNotCreateIllicitPurpose ()

wireDoesNotCreateCommonOperation : WireImpliesCommonOperation → ⊥
wireDoesNotCreateCommonOperation ()

rothschildWireDoesNotCreateFamilyWideAgency : RothschildWireImpliesFamilyWideAgency → ⊥
rothschildWireDoesNotCreateFamilyWideAgency ()

careOfApolloDoesNotCreateApolloPayer : CareOfApolloImpliesApolloPayer → ⊥
careOfApolloDoesNotCreateApolloPayer ()

------------------------------------------------------------------------
-- Next acquisition follows the money rather than expanding names blindly.
------------------------------------------------------------------------

data TransactionDebt : Set where
  rothschildWirePurpose : TransactionDebt
  rothschildUpstreamAccountSource : TransactionDebt
  blackMissing2012Wire : TransactionDebt
  blackMissingAdditionalWires : TransactionDebt
  wirePurposeDocumentJoin : TransactionDebt
  downstreamSouthernTrustUse : TransactionDebt

record TransactionAcquisition : Set where
  constructor transaction-acquisition
  field
    debt : TransactionDebt
    priority : Nat
    question : String
open TransactionAcquisition public

canonicalTransactionAcquisition : List TransactionAcquisition
canonicalTransactionAcquisition =
  transaction-acquisition rothschildWirePurpose 100
    "Acquire the originating instructions, memo/purpose, contracts or correspondence for the USD 10m Edmond de Rothschild (Suisse) SA and USD 14,999,980 Benjamin Edmond de Rothschild transfers to Southern Trust Company."
  ∷ transaction-acquisition downstreamSouthernTrustUse 100
    "Trace same-object downstream use of large Southern Trust inflows without assuming fungible account balance identifies source-specific expenditure."
  ∷ transaction-acquisition blackMissingAdditionalWires 99
    "Join EFTA00027019 and Treasury/SAR records to identify the additional approximately USD 12m of Black-account wires Senate Finance says were absent from Dechert's USD 158m total."
  ∷ transaction-acquisition blackMissing2012Wire 99
    "Acquire the November 2012 USD 5.5m wire identified by Senate Finance/Treasury but outside the currently enumerated EFTA00027019 Black rows."
  ∷ transaction-acquisition wirePurposeDocumentJoin 98
    "Join each Black-family/Elysium wire to a contract, invoice, tax structure, loan, gift or other contemporaneous purpose document rather than importing the aggregate advisory narrative."
  ∷ transaction-acquisition rothschildUpstreamAccountSource 97
    "Resolve the exact originating accounts/entities and signatory/beneficial-owner coordinates for the December 2015 Rothschild wires while distinguishing institution from individual."
  ∷ []
