module DASHI.Culture.MissingDeceasedTwentyScientistRound36HCBContractDerivativeIdentityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- ROUND 36: HCB CONTRACT-DERIVATIVE IDENTITY SURFACE
--
-- Search on the exact HCB contract number exposes person-bearing derivative
-- artefacts.  These can pay identity on the derivative object itself, but an
-- inventor list is not an exhaustive contract roster.  Absence of a retained
-- scientist from the currently acquired derivatives therefore cannot pay
-- non-participation on the wider HCB contract or programme.
------------------------------------------------------------------------

contractIdentifier : String
contractIdentifier = "FA9300-07-C-0001"

pelfreyPatentSource : Attribution.AttributedSource
pelfreyPatentSource = Attribution.mkNoDOISource
  "United States Patent and Trademark Office; Google Patents mirror"
  "US8596960B1 — Turbopump with a tapered hydrostatic bearing"
  "United States patent record"
  "2013"
  "https://patents.google.com/patent/US8596960B1/en"
  Attribution.governmentSource
  "Pays publication/application identity, inventor Philip C. Pelfrey, and the patent's government-support statement naming FA9300-07-C-0001; does not enumerate all contract personnel."
  Attribution.publicAttribution

pineraHuberCorrectionSource : Attribution.AttributedSource
pineraHuberCorrectionSource = Attribution.mkNoDOISource
  "United States Patent and Trademark Office"
  "Certificate of Correction for US8177489B1"
  "United States patent record"
  "2012"
  "https://patentimages.storage.googleapis.com/cb/d9/0b/0dd2a9e81a6e57/US8177489.pdf"
  Attribution.governmentSource
  "Pays inventor names Alex Pinera and Frank W. Huber and corrects the government-support paragraph to name FA9300-07-C-0001; does not enumerate all contract personnel."
  Attribution.publicAttribution

pelfreySourceRole : Snowball.SourceRoleSnowballReceipt pelfreyPatentSource
pelfreySourceRole = Snowball.canonicalSourceRoleSnowballReceipt pelfreyPatentSource

pineraHuberSourceRole : Snowball.SourceRoleSnowballReceipt pineraHuberCorrectionSource
pineraHuberSourceRole = Snowball.canonicalSourceRoleSnowballReceipt pineraHuberCorrectionSource

record ContractDerivativeIdentityReceipt : Set where
  constructor contract-derivative-identity-receipt
  field
    source : Attribution.AttributedSource
    derivativeObject : String
    derivativeContractIdentifier : String
    namedTechnicalPeople : String
    sourceDate : String
    exactContractIdentifierPaid : Bool
    namedDerivativeIdentityPaid : Bool
    retainedScientistNamed : Bool
    monicaExactContractRolePaid : Bool
    mccaslandExactContractRolePaid : Bool
    whatItPays : String
    whatItDoesNotPay : String

open ContractDerivativeIdentityReceipt public

pelfreyDerivativeReceipt : ContractDerivativeIdentityReceipt
pelfreyDerivativeReceipt = contract-derivative-identity-receipt
  pelfreyPatentSource
  "US8596960B1 / tapered hydrostatic bearing"
  contractIdentifier
  "Philip C. Pelfrey"
  "filed 2010-11-08; published 2013-12-03"
  true
  true
  false
  false
  false
  "a named inventor on a derivative technical object whose patent explicitly names FA9300-07-C-0001 government support"
  "an exhaustive HCB personnel roster, Monica Jacinto's exact contract role, Neil McCasland's exact contract role, same-task membership, H2, or H3"

pineraHuberDerivativeReceipt : ContractDerivativeIdentityReceipt
pineraHuberDerivativeReceipt = contract-derivative-identity-receipt
  pineraHuberCorrectionSource
  "US8177489B1 certificate of correction"
  contractIdentifier
  "Alex Pinera; Frank W. Huber"
  "certificate dated 2012-08-28"
  true
  true
  false
  false
  false
  "named inventors on a patent record whose corrected government-support paragraph explicitly names FA9300-07-C-0001"
  "an exhaustive HCB personnel roster, Monica Jacinto's exact contract role, Neil McCasland's exact contract role, same-task membership, H2, or H3"

round36DerivativeReceipts : List ContractDerivativeIdentityReceipt
round36DerivativeReceipts = pelfreyDerivativeReceipt ∷ pineraHuberDerivativeReceipt ∷ []

round36DerivativeReceiptCount : Nat
round36DerivativeReceiptCount = 2

round36RetainedScientistDerivativeCount : Nat
round36RetainedScientistDerivativeCount = 0

derivativeIdentityCanPayNamedTechnicalParticipation : Bool
derivativeIdentityCanPayNamedTechnicalParticipation = true

derivativeInventorListIsNotExhaustiveContractRoster : Bool
derivativeInventorListIsNotExhaustiveContractRoster = true

absenceFromDerivativeCannotPayNonParticipation : Bool
absenceFromDerivativeCannotPayNonParticipation = true

contractNumberMatchDoesNotCollapseDerivativeRoles : Bool
contractNumberMatchDoesNotCollapseDerivativeRoles = true

currentDerivativesNameMonica : Bool
currentDerivativesNameMonica = false

currentDerivativesNameMcCasland : Bool
currentDerivativesNameMcCasland = false

round36H2PaidCount : Nat
round36H2PaidCount = 0

round36H3PaidCount : Nat
round36H3PaidCount = 0

round36Pareto : String
round36Pareto = "Continue snowballing FA9300-07-C-0001 into contemporaneous patents, technical papers, contract modifications and programme-review/distribution records. Promote only literal person-bearing exact-role receipts. The current derivative inventor lists add named technical identities but are not exhaustive rosters and cannot prove Monica or McCasland non-participation by absence."
