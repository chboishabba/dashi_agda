module DASHI.Culture.BlochfieldCrossPlatformIdentityConvergenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT
import DASHI.Culture.BlochfieldCreatorGenealogySnowballExact as Creator

------------------------------------------------------------------------
-- BLOCHFIELD CROSS-PLATFORM IDENTITY CONVERGENCE
--
-- The surviving convergence is stronger than display-name similarity alone:
--   * X mirror: Yasmin Anacreto / @msiyasmsi, web3 fullstack context and
--     profile coordinate @gmnevergiveup;
--   * Link3: 0xyasanacreto.cyber, featured content explicitly attributed to
--     Yasmin Anacreto; the inspected "What's a Galactic G?" snippet describes
--     web3 activity and explicitly names @Galxe.
--
-- Correction: no inspected source links "Galactic G" to @gmnevergiveup.
-- That lexical/project relation is therefore unpaid and must not be used as an
-- identity bridge.  The remaining convergence is same display name + web3
-- context, still insufficient for authenticated same-person identity.
------------------------------------------------------------------------

record CrossPlatformConvergenceCandidate : Set where
  constructor cross-platform-convergence-candidate
  field
    xObservation : OSINT.OSINTObservation
    link3Candidate : Creator.CrossPlatformIdentityCandidate
    sharedDisplayName : String
    sharedContext : String
    xProfileCoordinate : String
    link3FeaturedCoordinate : String
    inspectedLink3Reference : String
    convergenceStrongerThanNameAlone : Bool
    convergenceStrongerThanNameAloneIsTrue :
      convergenceStrongerThanNameAlone ≡ true
    galacticGToGmNeverGiveUpRelationPaid : Bool
    galacticGToGmNeverGiveUpRelationPaidIsFalse :
      galacticGToGmNeverGiveUpRelationPaid ≡ false
    exactSamePersonIdentityPaid : Bool
    exactSamePersonIdentityPaidIsFalse :
      exactSamePersonIdentityPaid ≡ false

open CrossPlatformConvergenceCandidate public

link3XGalacticGConvergenceCandidate : CrossPlatformConvergenceCandidate
link3XGalacticGConvergenceCandidate =
  cross-platform-convergence-candidate
    Creator.creatorProfileObservation
    Creator.link3IdentityCandidate
    "Yasmin Anacreto"
    "web3"
    "@gmnevergiveup"
    "What's a Galactic G?"
    "inspected Link3 snippet explicitly names @Galxe; no gmnevergiveup relation located"
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Keep the ordered payment frontier fail-closed.
------------------------------------------------------------------------

crossPlatformIdentityWeldStillUnpaid : Creator.GenealogyStanding
crossPlatformIdentityWeldStillUnpaid =
  Creator.genealogyStanding Creator.crossPlatformIdentityWeld

data MultiCoordinateConvergencePaysSamePerson : Set where

data SharedWeb3ContextPaysSamePerson : Set where

data GalacticGNamesGmNeverGiveUp : Set where

multiCoordinateConvergenceDoesNotPaySamePerson :
  MultiCoordinateConvergencePaysSamePerson → ⊥
multiCoordinateConvergenceDoesNotPaySamePerson ()

sharedWeb3ContextDoesNotPaySamePerson :
  SharedWeb3ContextPaysSamePerson → ⊥
sharedWeb3ContextDoesNotPaySamePerson ()

galacticGDoesNotPayGmNeverGiveUpRelation :
  GalacticGNamesGmNeverGiveUp → ⊥
galacticGDoesNotPayGmNeverGiveUpRelation ()

------------------------------------------------------------------------
-- Semantic checksum:
--
--   same display name + shared web3 context
--     > display-name similarity alone for discovery
--
--   "Galactic G" snippet -> @Galxe
--   "Galactic G" -/-> @gmnevergiveup  (unpaid)
--
--   same display name + shared web3 context
--     != authenticated cross-platform identity
--
-- The correction prunes a suggestive but unsupported lexical edge while
-- retaining the lower-strength convergence that the inspected sources pay.
-- The next useful identity receipt remains a native mutual link, signed
-- wallet/account assertion, authenticated platform link, or explicit creator
-- statement connecting the accounts.
------------------------------------------------------------------------
