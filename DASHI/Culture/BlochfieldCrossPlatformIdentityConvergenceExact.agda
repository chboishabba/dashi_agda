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
-- A stronger identity candidate than name similarity alone:
--   * X mirror: Yasmin Anacreto / @msiyasmsi, profile names @gmnevergiveup;
--   * Link3: 0xyasanacreto.cyber, featured content explicitly attributed to
--     Yasmin Anacreto and titled "What's a Galactic G?".
--
-- The shared display name plus Galactic-G / gmnevergiveup thematic coordinate
-- materially strengthens discovery convergence, but still does NOT pay exact
-- same-person identity.  No native mutual link, signed wallet assertion,
-- platform-authenticated account link, or creator statement was acquired.
------------------------------------------------------------------------

record CrossPlatformConvergenceCandidate : Set where
  constructor cross-platform-convergence-candidate
  field
    xObservation : OSINT.OSINTObservation
    link3Candidate : Creator.CrossPlatformIdentityCandidate
    sharedDisplayName : String
    xProjectCoordinate : String
    link3FeaturedCoordinate : String
    convergenceStrongerThanNameAlone : Bool
    convergenceStrongerThanNameAloneIsTrue :
      convergenceStrongerThanNameAlone ≡ true
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
    "@gmnevergiveup"
    "What's a Galactic G?"
    true refl
    false refl

------------------------------------------------------------------------
-- Keep the ordered payment frontier fail-closed.
------------------------------------------------------------------------

crossPlatformIdentityWeldStillUnpaid : Creator.GenealogyStanding
crossPlatformIdentityWeldStillUnpaid =
  Creator.genealogyStanding Creator.crossPlatformIdentityWeld

data MultiCoordinateConvergencePaysSamePerson : Set where

data ThematicProjectOverlapPaysSamePerson : Set where

multiCoordinateConvergenceDoesNotPaySamePerson :
  MultiCoordinateConvergencePaysSamePerson → ⊥
multiCoordinateConvergenceDoesNotPaySamePerson ()

thematicProjectOverlapDoesNotPaySamePerson :
  ThematicProjectOverlapPaysSamePerson → ⊥
thematicProjectOverlapDoesNotPaySamePerson ()

------------------------------------------------------------------------
-- Semantic checksum:
--
--   same display name + shared project vocabulary
--     > name similarity alone for discovery
--
--   same display name + shared project vocabulary
--     != authenticated cross-platform identity
--
-- The Pareto therefore improves search priority without changing conclusion
-- payment.  The next useful identity receipt would be a native mutual link,
-- signed wallet/account assertion, authenticated platform link, or explicit
-- creator statement connecting the accounts.
------------------------------------------------------------------------
