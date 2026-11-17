module DASHI.Cognition.EpsteinWexnerTrusteeTenureBoundary20261015Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Cognition.EpsteinWexnerTrustInstrumentAuthority20261015Exact as Instrument
import DASHI.Cognition.EpsteinWexnerTrustBearInvestmentAuthority20261015Exact as BearAuthority

------------------------------------------------------------------------
-- WEXNER CHILDREN'S TRUST II — TRUSTEE TENURE BOUNDS
--
-- Positive neutral records pay creation/SEC trustee dates. Bear's FINRA answer
-- supplies later attributed trustee-capacity and removal assertions, but the
-- removal footnote cites a Reuters report rather than an attached removal deed.
-- Therefore 2008 is an attributed endpoint, not the exact legal termination
-- date/instrument.
------------------------------------------------------------------------

data TenureSource : Set where
  executedTrustAgreement : TenureSource
  secSchedule13DSignature : TenureSource
  adversarialBearPleading : TenureSource
  adversarialPleadingCitingMedia : TenureSource
  successorOrRemovalInstrument : TenureSource

record TenureReceipt : Set where
  constructor tenure-receipt
  field
    date : String
    sourceClass : TenureSource
    source : String
    boundedFinding : String
    epsteinTrusteeStatusPaid : Bool
    neutralGoverningOrDisclosureRecord : Bool
open TenureReceipt public

trustCreation1998 : TenureReceipt
trustCreation1998 = tenure-receipt
  "1998-02-25" executedTrustAgreement
  "EFTA01481286 / JPM-SDNY-00002596; execution EFTA01480437"
  "Executed Wexner Children's Trust II agreement identifies Leslie H. Wexner as grantor and Jeffrey E. Epstein as trustee; the execution page records Epstein signing as trustee."
  true true

secSignature2002 : TenureReceipt
secSignature2002 = tenure-receipt
  "2002-06-12" secSchedule13DSignature
  "Limited Brands Schedule 13D/A signature page, issuer-hosted SEC filing copy"
  "The reporting-person signature page lists THE WEXNER CHILDREN'S TRUST II and is signed by Jeffrey E. Epstein expressly as Trustee. This independently pays trustee status as of June 2002."
  true true

secSignature2003 : TenureReceipt
secSignature2003 = tenure-receipt
  "2003-08-29" secSchedule13DSignature
  "Limited Brands beneficial-ownership filing, issuer-hosted SEC filing copy"
  "The August 29 2003 signature page again lists THE WEXNER CHILDREN'S TRUST II and is signed by Jeffrey E. Epstein expressly as Trustee. This is the latest neutral public trustee signature paid in the current sweep; it does not establish a terminal date."
  true true

bearTrusteeAssertion2006 : TenureReceipt
bearTrusteeAssertion2006 = tenure-receipt
  "2006-11" adversarialBearPleading
  "EFTA00294820 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that Epstein acted in his capacity as trustee of Wexner Children's Trust II for an additional USD20m ABS-fund investment. This pays the attributed assertion and its timing/capacity, not a neutral subscription or trustee certificate."
  true false

bearTrusteeAssertion2007 : TenureReceipt
bearTrusteeAssertion2007 = tenure-receipt
  "2007-04" adversarialBearPleading
  "EFTA00294821 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents separately state that Epstein acted in trustee capacity for a USD10m Europe Long/Short investment in 2007. This extends the attributed litigation chronology but is not promoted to the same evidentiary class as the trust agreement/SEC signatures."
  true false

bearRemovalAssertion2008 : TenureReceipt
bearRemovalAssertion2008 = tenure-receipt
  "2008" adversarialPleadingCitingMedia
  "EFTA00294820 footnote 4 — Bear Stearns Respondents' FINRA Statement of Answer, citing Jessica Hall/Reuters DealZone, 11 Feb 2008"
  "In the same footnote describing the USD20m trust investment, Bear respondents state that Epstein 'was removed as trustee of the trust in 2008.' The footnote cites contemporaneous Reuters reporting rather than attaching the removal/resignation instrument. This pays an attributed 2008 endpoint claim, not the exact legal removal date or successor identity."
  false false

record TenureBoundary : Set where
  constructor tenure-boundary
  field
    trusteeAtCreationPaid : Bool
    trusteeIn2002SECRecordPaid : Bool
    trusteeIn2003SECRecordPaid : Bool
    bearAssertsTrusteeCapacity2006And2007 : Bool
    bearAssertsRemovalIn2008 : Bool
    exactRemovalOrSuccessorDatePaid : Bool
    exactRemovalInstrumentPaid : Bool
    absenceOfLaterSignatureImpliesRemoval : Bool
    pleadingTrusteeLabelEqualsRemovalInstrument : Bool
    tenureThrough2007AdjudicatedByTheseRecords : Bool
open TenureBoundary public

canonicalTenureBoundary : TenureBoundary
canonicalTenureBoundary = tenure-boundary
  true true true true true false false false false false

data MissingLaterSignatureImpliesRemoval : Set where
data PleadingImpliesNeutralTenureCertificate : Set where
data RemovalAssertionImpliesRemovalInstrument : Set where
data EarlierTrusteeStatusImpliesIndefiniteAuthority : Set where

missingSignatureDoesNotCreateRemoval : MissingLaterSignatureImpliesRemoval → ⊥
missingSignatureDoesNotCreateRemoval ()

pleadingDoesNotCreateNeutralCertificate : PleadingImpliesNeutralTenureCertificate → ⊥
pleadingDoesNotCreateNeutralCertificate ()

removalAssertionDoesNotCreateInstrument : RemovalAssertionImpliesRemovalInstrument → ⊥
removalAssertionDoesNotCreateInstrument ()

earlierStatusDoesNotCreateIndefiniteAuthority : EarlierTrusteeStatusImpliesIndefiniteAuthority → ⊥
earlierStatusDoesNotCreateIndefiniteAuthority ()

------------------------------------------------------------------------
-- Pareto: terminal legal transition is now the authority chronology debt.
------------------------------------------------------------------------

data TenureDebt : Set where
  successorRemovalInstrument : TenureDebt
  allTrustAmendments : TenureDebt
  trusteeCertificates2004to2008 : TenureDebt
  neutralBearAccountAuthorityRecord : TenureDebt
  contemporaneousReutersUnderlyingSources : TenureDebt

record TenureAcquisition : Set where
  constructor tenure-acquisition
  field
    debt : TenureDebt
    priority : Nat
    question : String
open TenureAcquisition public

canonicalTenureAcquisition : List TenureAcquisition
canonicalTenureAcquisition =
  tenure-acquisition successorRemovalInstrument 100
    "Acquire the signed resignation/removal/successor-trustee instrument that gives the exact legal terminal date and successor; the 2008 Bear/Reuters statement is not that instrument." ∷
  tenure-acquisition allTrustAmendments 100
    "Acquire the complete amendment/restatement chain between the 1998 trust and the terminal successor/removal instrument." ∷
  tenure-acquisition trusteeCertificates2004to2008 99
    "Acquire dated bank/broker/SEC trustee certificates or signature pages during 2004-2008 to tighten the neutral positive tenure interval beyond the August 2003 SEC signature." ∷
  tenure-acquisition neutralBearAccountAuthorityRecord 99
    "Acquire Bear account/subscription records showing who was recognized as trustee/signatory at the dates of the 2006/07 investments." ∷
  tenure-acquisition contemporaneousReutersUnderlyingSources 95
    "Recover the February 2008 Reuters report and any primary source on which it relied; media citation can nominate but not replace the legal transition instrument."
  ∷ []
