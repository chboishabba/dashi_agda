module DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyLibraryLongitudinalIncidenceExact as Longitudinal

------------------------------------------------------------------------
-- PSEUDONYMOUS NETWORK FEATURES OVER THE ADMITTED PEOPLE'S LIBRARY GRAPH.
--
-- DASHI-derived descriptive statistics only. Participant identity is carried
-- only by stable opaque tokens in the source graph; no raw-name table is
-- required or reconstructed here.
--
-- Ratios are stored as exact Nat numerator/denominator pairs rather than
-- floating-point approximations:
--   density = E / (|P|*|I|)
--   participant concentration = sum(deg_P^2) / E^2
--   issue concentration = sum(deg_I^2) / E^2
--   returning share = returning pseudonyms / observed pseudonyms this meeting
------------------------------------------------------------------------

record NetworkFeatureRow : Set where
  constructor networkFeatureRow
  field
    meetingLabel : String
    edgeCount : Nat
    pseudonymousParticipantCount : Nat
    issueCount : Nat
    densityNumerator : Nat
    densityDenominator : Nat
    participantHHINumerator : Nat
    participantHHIDenominator : Nat
    issueHHINumerator : Nat
    issueHHIDenominator : Nat
    returningParticipantCount : Nat
    returningParticipantDenominator : Nat

open NetworkFeatureRow public

featureRowCount : List NetworkFeatureRow → Nat
featureRowCount [] = 0
featureRowCount (_ ∷ xs) = suc (featureRowCount xs)

oct22Features : NetworkFeatureRow
oct22Features = networkFeatureRow "2011-10-22" 18 11 9 18 99 36 324 42 324 0 11

nov20Features : NetworkFeatureRow
nov20Features = networkFeatureRow "2011-11-20" 9 6 9 9 54 17 81 9 81 4 6

nov28Features : NetworkFeatureRow
nov28Features = networkFeatureRow "2011-11-28" 7 6 7 7 42 9 49 7 49 3 6

dec11Features : NetworkFeatureRow
dec11Features = networkFeatureRow "2011-12-11" 11 8 7 11 56 17 121 31 121 5 8

jan08Features : NetworkFeatureRow
jan08Features = networkFeatureRow "2012-01-08" 7 5 7 7 35 13 49 7 49 4 5

canonicalNetworkFeatureRows : List NetworkFeatureRow
canonicalNetworkFeatureRows =
  oct22Features ∷ nov20Features ∷ nov28Features ∷ dec11Features ∷ jan08Features ∷ []

record NetworkFeatureBoundary : Set where
  constructor networkFeatureBoundary
  field
    derivedFromAdmittedPseudonymousRows : Bool
    completeNamedParticipantIssueMatrixRequired : Bool
    pseudonymousRelationalFeaturesUseful : Bool
    spellingVariantsAutomaticallyUnified : Bool
    returningTokenProvesRealWorldIdentity : Bool
    networkFeaturesAreCoordinationCost : Bool
    networkFeaturesAreCausalEffects : Bool
    crossSourceRegimesSilentlyPooled : Bool

open NetworkFeatureBoundary public

canonicalNetworkFeatureBoundary : NetworkFeatureBoundary
canonicalNetworkFeatureBoundary =
  networkFeatureBoundary true false true false false false false false

canonicalPseudonymousNetworkFeatureReceipt : GenericReceipt.GenericReceipt
canonicalPseudonymousNetworkFeatureReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "pseudonymous People's Library network features"
    "DASHI.Governance.OccupyPseudonymousNetworkFeaturesExact"
    "canonicalNetworkFeatureBoundary"
    "records exact edge, pseudonymous-participant, issue, density, degree-concentration and prior-meeting recurrence coordinates for the five admitted People's Library graph meetings without retaining raw participant names"
    "the features describe only the admitted coded graph; pseudonym recurrence is not proof of real-world identity equivalence, spelling variants are not merged automatically, and density/concentration/recurrence are not coordination cost or causal effects"
    "agda -i . DASHI/Governance/OccupyPseudonymousNetworkFeaturesRegression.agda"
