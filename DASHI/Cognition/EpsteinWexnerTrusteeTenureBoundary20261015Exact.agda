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
-- WEXNER CHILDREN'S TRUST II — TRUSTEE TENURE LOWER BOUND
--
-- This owner records positive dated evidence only.  An observed trustee
-- signature gives a lower bound on tenure; absence of a later indexed signature
-- is not a removal date.  The Bear 2006/07 respondent assertions are kept in a
-- different source class from the executed trust and SEC signature pages.
------------------------------------------------------------------------

data TenureSource : Set where
  executedTrustAgreement : TenureSource
  secSchedule13DSignature : TenureSource
  adversarialBearPleading : TenureSource
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
  "EFTA00294815..EFTA00294822 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents state that Epstein acted in his capacity as trustee of Wexner Children's Trust II for a USD20m ABS-fund investment. This is later-period source evidence of asserted trustee capacity, but it remains a party pleading rather than the successor/removal instrument or a neutral trustee certificate."
  true false

bearTrusteeAssertion2007 : TenureReceipt
bearTrusteeAssertion2007 = tenure-receipt
  "2007-04" adversarialBearPleading
  "EFTA00294821 — Bear Stearns Respondents' FINRA Statement of Answer"
  "Bear respondents separately state that Epstein acted in trustee capacity for a USD10m Europe Long/Short investment in 2007. This extends the attributed litigation chronology but is not promoted to the same evidentiary class as the trust agreement/SEC signatures."
  true false

record TenureBoundary : Set where
  constructor tenure-boundary
  field
    trusteeAtCreationPaid : Bool
    trusteeIn2002SECRecordPaid : Bool
    trusteeIn2003SECRecordPaid : Bool
    bearAssertsTrusteeCapacity2006And2007 : Bool
    exactRemovalOrSuccessorDatePaid : Bool
    absenceOfLaterSignatureImpliesRemoval : Bool
    pleadingTrusteeLabelEqualsRemovalInstrument : Bool
    tenureThrough2007AdjudicatedByTheseRecords : Bool
open TenureBoundary public

canonicalTenureBoundary : TenureBoundary
canonicalTenureBoundary = tenure-boundary
  true true true true false false false false

data MissingLaterSignatureImpliesRemoval : Set where
data PleadingImpliesNeutralTenureCertificate : Set where
data EarlierTrusteeStatusImpliesIndefiniteAuthority : Set where

missingSignatureDoesNotCreateRemoval : MissingLaterSignatureImpliesRemoval → ⊥
missingSignatureDoesNotCreateRemoval ()

pleadingDoesNotCreateNeutralCertificate : PleadingImpliesNeutralTenureCertificate → ⊥
pleadingDoesNotCreateNeutralCertificate ()

earlierStatusDoesNotCreateIndefiniteAuthority : EarlierTrusteeStatusImpliesIndefiniteAuthority → ⊥
earlierStatusDoesNotCreateIndefiniteAuthority ()

------------------------------------------------------------------------
-- Pareto: terminal tenure is now the only authority chronology debt.
------------------------------------------------------------------------

data TenureDebt : Set where
  successorRemovalInstrument : TenureDebt
  allTrustAmendments : TenureDebt
  trusteeCertificates2004to2008 : TenureDebt
  neutralBearAccountAuthorityRecord : TenureDebt

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
    "Acquire the instrument that removes/replaces Epstein or otherwise terminates his Wexner Children’s Trust II trusteeship; do not derive an end date from silence." ∷
  tenure-acquisition allTrustAmendments 100
    "Acquire the complete amendment/restatement chain between the 1998 trust and the terminal successor/removal instrument." ∷
  tenure-acquisition trusteeCertificates2004to2008 99
    "Acquire dated bank/broker/SEC trustee certificates or signature pages during 2004-2008 to tighten the positive tenure interval beyond the neutral August 2003 signature and independently test the later Bear pleading assertions." ∷
  tenure-acquisition neutralBearAccountAuthorityRecord 99
    "Acquire Bear account/subscription records showing who was recognized as trustee/signatory at the dates of the 2006/07 investments."
  ∷ []
