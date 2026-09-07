module DASHI.Interop.AristotleReliableSourceConsumerAdequacyBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.ProvenanceSensitiveConsumerAdequacyBidiExact as Adequacy
import DASHI.Interop.AristotleRankQualifierPropertyEngineBoundary as Aristotle

-- Archive donor: RequestProject.Provenance full/sourced/reliable restrictions.
data ProvenanceFragment : Set where
  fullFragment sourcedFragment reliableFragment : ProvenanceFragment

record ReliableConsumerAdequacyReceipt : Set where
  constructor reliable-consumer-adequacy-receipt
  field
    consumerReference : String
    fullSupportReference : String
    sourcedSupportReference : String
    reliableSupportReference : String
    fullVisibleCountAdequate : Bool
    reliableIndependentSupportAdequate : Bool
open ReliableConsumerAdequacyReceipt public

-- Visible multiplicity in the full fragment is not the same thing as
-- independently adequate reliable-source support.
data FullSupportCountImpliesReliableAdequacy : Set where
fullCountDoesNotManufactureReliableAdequacy :
  FullSupportCountImpliesReliableAdequacy → ⊥
fullCountDoesNotManufactureReliableAdequacy ()

-- Restriction can lose support but cannot create new source authority.
data ReliableRestrictionCreatesNewFact : Set where
reliableRestrictionDoesNotInventSupport :
  ReliableRestrictionCreatesNewFact → ⊥
reliableRestrictionDoesNotInventSupport ()

record AristotleReliableAdequacyBoundary : Set where
  constructor aristotle-reliable-adequacy-boundary
  field
    fullSourcedReliableRemainDistinct : Bool
    visibleCountEqualsIndependentReliableSupport : Bool
    reliableRestrictionMayLoseSupport : Bool
    reliableRestrictionInventsSupport : Bool
    provenanceMayBeConsumerAdequacyInput : Bool

canonicalAristotleReliableAdequacyBoundary :
  AristotleReliableAdequacyBoundary
canonicalAristotleReliableAdequacyBoundary =
  aristotle-reliable-adequacy-boundary true false true false true

reliableAdequacyStatement : String
reliableAdequacyStatement =
  "Aristotle provenance restrictions support a consumer-sensitive distinction between full, sourced and reliable evidence. A pattern visible in the full fragment does not automatically satisfy a consumer requiring independently adequate reliable support; restriction may remove derivable support but does not invent new support or authority."
