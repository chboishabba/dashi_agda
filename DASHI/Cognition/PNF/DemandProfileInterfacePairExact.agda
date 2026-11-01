{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.DemandProfileInterfacePairExact where

open import Agda.Builtin.Equality using (_≡_; refl)

------------------------------------------------------------------------
-- DEMAND INTERFACE AND CANDIDATE-PROFILE INTERFACE ARE DISTINCT COORDINATES
--
-- The live wildcard gate exposed a generic identity mistake: the interface that
-- exports/owns a demand need not be the interface whose actor-profile carrier
-- supplies candidate provenance.  Matching graph revisions do not identify
-- these coordinates.
------------------------------------------------------------------------

record DemandProfilePair (Interface Revision : Set) : Set₁ where
  constructor demandProfilePair
  field
    demandInterface : Interface
    profileInterface : Interface
    demandRevision : Revision
    profileRevision : Revision

open DemandProfilePair public

record PairIndexedParity
  (Interface Revision Observation : Set) : Set₁ where
  field
    pair : DemandProfilePair Interface Revision
    boundedObservation : Observation
    legacyObservation : Observation
    observationParity : boundedObservation ≡ legacyObservation

open PairIndexedParity public

pairIndexedParityIsExact :
  ∀ {Interface Revision Observation : Set}
    (certificate : PairIndexedParity Interface Revision Observation) →
  boundedObservation certificate ≡ legacyObservation certificate
pairIndexedParityIsExact certificate = observationParity certificate

------------------------------------------------------------------------
-- Revision agreement is useful freshness evidence but cannot manufacture
-- interface identity.  There is deliberately no eliminator from equal revisions
-- to equal interface coordinates.
------------------------------------------------------------------------

data RevisionEqualityImpliesInterfaceEqualityPermission : Set where

revisionEqualityCannotIdentifyInterfaces :
  ∀ {Interface Revision : Set}
    {demandI profileI : Interface}
    {demandR profileR : Revision} →
  demandR ≡ profileR →
  RevisionEqualityImpliesInterfaceEqualityPermission →
  demandI ≡ profileI
revisionEqualityCannotIdentifyInterfaces same ()

------------------------------------------------------------------------
-- Benchmark comparability is also pair-indexed: measurements may only be
-- compared directly when they refer to the same demand/profile interface pair.
------------------------------------------------------------------------

record PairIndexedMeasurement
  (Interface Revision Cost : Set) : Set₁ where
  field
    measuredPair : DemandProfilePair Interface Revision
    cost : Cost

open PairIndexedMeasurement public

samePairMeasurement :
  ∀ {Interface Revision Cost : Set}
    {left right : PairIndexedMeasurement Interface Revision Cost} →
  measuredPair left ≡ measuredPair right →
  measuredPair left ≡ measuredPair right
samePairMeasurement refl = refl
