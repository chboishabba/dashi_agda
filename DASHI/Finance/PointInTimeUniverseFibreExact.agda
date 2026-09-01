module DASHI.Finance.PointInTimeUniverseFibreExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Finance.TemporalMarketFibreExact as Temporal

------------------------------------------------------------------------
-- Point-in-time universe semantics.
--
-- Universe membership is a fibre-local datum.  A later constituent set may
-- not be transported backwards and silently reused as the earlier universe.
------------------------------------------------------------------------

record UniverseFibre : Set where
  constructor universeFibre
  field
    universeTime : Nat
    constituentSet : String
    membershipProvenance : String
    dynamicHistoricalPool : Bool

open UniverseFibre public

record PITUniverseWitness (u : UniverseFibre) : Set where
  constructor pitUniverseWitness
  field
    historicalPoolIsDynamic : dynamicHistoricalPool u ≡ true
    membershipKnownAtThatTime : Bool
    membershipKnownAtThatTimeIsTrue : membershipKnownAtThatTime ≡ true

open PITUniverseWitness public

record UniverseTransport (source target : UniverseFibre) : Set where
  constructor universeTransport
  field
    forward : Temporal.ForwardPath (universeTime source) (universeTime target)
    provenancePreserved : Bool
    provenancePreservedIsTrue : provenancePreserved ≡ true
    membershipInvented : Bool
    membershipInventedIsFalse : membershipInvented ≡ false

open UniverseTransport public

historical0 : UniverseFibre
historical0 =
  universeFibre 0
    "historical constituents at t0"
    "constituent-history receipt@t0"
    true

historical1 : UniverseFibre
historical1 =
  universeFibre 1
    "historical constituents at t1"
    "constituent-history receipt@t1"
    true

staticLaterList : UniverseFibre
staticLaterList =
  universeFibre 1
    "static later S&P 500 list"
    "later-list membership"
    false

historical0PIT : PITUniverseWitness historical0
historical0PIT = pitUniverseWitness refl true refl

historical1PIT : PITUniverseWitness historical1
historical1PIT = pitUniverseWitness refl true refl

------------------------------------------------------------------------
-- A future/static universe cannot be pushed backwards through the lawful
-- temporal transport relation.  This is the formal shape of survivorship /
-- universe-selection leakage.
------------------------------------------------------------------------

staticLaterToHistorical0Impossible :
  UniverseTransport staticLaterList historical0 → ⊥
staticLaterToHistorical0Impossible tr =
  Temporal.noBackwardPath10 (forward tr)

record UniverseLeakageBoundary : Set where
  constructor universeLeakageBoundary
  field
    featurePITImpliesUniversePIT : Bool
    featurePITImpliesUniversePITIsFalse :
      featurePITImpliesUniversePIT ≡ false
    staticLaterMembershipIsHistoricalEvidence : Bool
    staticLaterMembershipIsHistoricalEvidenceIsFalse :
      staticLaterMembershipIsHistoricalEvidence ≡ false

canonicalUniverseLeakageBoundary : UniverseLeakageBoundary
canonicalUniverseLeakageBoundary =
  universeLeakageBoundary false refl false refl

universeBoundaryStatement : String
universeBoundaryStatement =
  "Point-in-time feature construction does not imply point-in-time universe construction; later membership requires an explicit lawful forward provenance path and cannot be transported backwards."
