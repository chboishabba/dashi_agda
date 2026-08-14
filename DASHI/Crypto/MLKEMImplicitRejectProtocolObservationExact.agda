module DASHI.Crypto.MLKEMImplicitRejectProtocolObservationExact where

------------------------------------------------------------------------
-- ML-KEM IMPLICIT-REJECTION ROUTE VS EXTERNAL OBSERVATION
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS 203 Algorithm 18 computes a secret comparison c != c' and selects the
-- fallback key J(z || c) on mismatch.  The comparison flag is secret
-- intermediate data and may not be returned.  This module separates existence
-- of the internal route from external observability of that route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)

import DASHI.Crypto.BlueTeamAdversaryObservationExact as Observation

------------------------------------------------------------------------
-- Route-bearing decapsulation abstraction.
------------------------------------------------------------------------

data DecapsulationRoute : Set where
  candidateRoute fallbackRoute : DecapsulationRoute

record RoutedProtocolSurface : Set₁ where
  constructor routedProtocolSurface
  field
    Hidden Public Ciphertext ObservationValue : Set
    project : Hidden → Public
    route : Hidden → Ciphertext → DecapsulationRoute
    observe : Hidden → Ciphertext → ObservationValue

open RoutedProtocolSurface public

asAdversarySystem : RoutedProtocolSurface → Observation.BlueTeamAdversarySystem
asAdversarySystem system =
  Observation.blueTeamAdversarySystem
    (Hidden system)
    (Public system)
    (Ciphertext system)
    (ObservationValue system)
    (project system)
    (observe system)

record InternalRouteDifference
    (system : RoutedProtocolSurface) : Set where
  constructor internalRouteDifference
  field
    left right : Hidden system
    samePublic : project system left ≡ project system right
    ciphertext : Ciphertext system
    routesDiffer :
      route system left ciphertext ≡ route system right ciphertext → ⊥

open InternalRouteDifference public

record ObservableRouteSplit
    (system : RoutedProtocolSurface) : Set where
  constructor observableRouteSplit
  field
    left right : Hidden system
    samePublic : project system left ≡ project system right
    ciphertext : Ciphertext system
    observationsDiffer :
      observe system left ciphertext ≡ observe system right ciphertext → ⊥

open ObservableRouteSplit public

observableRouteSplitGivesHiddenDependentObservation :
  ∀ {system : RoutedProtocolSurface} →
  ObservableRouteSplit system →
  Observation.HiddenDependentSplit (asAdversarySystem system)
observableRouteSplitGivesHiddenDependentObservation split =
  Observation.hiddenDependentSplit
    (left split)
    (right split)
    (samePublic split)
    (ciphertext split)
    (observationsDiffer split)

------------------------------------------------------------------------
-- Finite regression: internal route difference can exist while external
-- observation is constant.  Directly exporting the route would split the fibre.
------------------------------------------------------------------------

routeToBool : DecapsulationRoute → Bool
routeToBool candidateRoute = false
routeToBool fallbackRoute = true

opaqueRouteSurface : RoutedProtocolSurface
opaqueRouteSurface =
  routedProtocolSurface
    DecapsulationRoute ⊤ ⊤ Bool
    (λ hidden → tt)
    (λ hidden ciphertext → hidden)
    (λ hidden ciphertext → false)

opaqueInternalRouteDifference : InternalRouteDifference opaqueRouteSurface
opaqueInternalRouteDifference =
  internalRouteDifference candidateRoute fallbackRoute refl tt different
  where
  different : candidateRoute ≡ fallbackRoute → ⊥
  different ()

opaqueObservationPublicFactored :
  Observation.PublicFactored (asAdversarySystem opaqueRouteSurface)
opaqueObservationPublicFactored =
  Observation.publicFactored
    (λ public ciphertext → false)
    (λ hidden ciphertext → refl)

directRouteSurface : RoutedProtocolSurface
directRouteSurface =
  routedProtocolSurface
    DecapsulationRoute ⊤ ⊤ Bool
    (λ hidden → tt)
    (λ hidden ciphertext → hidden)
    (λ hidden ciphertext → routeToBool hidden)

directRouteObservableSplit : ObservableRouteSplit directRouteSurface
directRouteObservableSplit =
  observableRouteSplit candidateRoute fallbackRoute refl tt different
  where
  different : false ≡ true → ⊥
  different ()

directRouteLeakIsHiddenDependent :
  Observation.HiddenDependentSplit (asAdversarySystem directRouteSurface)
directRouteLeakIsHiddenDependent =
  observableRouteSplitGivesHiddenDependentObservation directRouteObservableSplit

------------------------------------------------------------------------
-- Boundary: FIPS explicitly forbids directly returning the comparison flag;
-- downstream accept/retry/timing/confirmation behaviour must be analysed as a
-- separate observation coordinate and needs its own split witness.
------------------------------------------------------------------------

record ImplicitRejectObservationBoundary : Set where
  constructor implicitRejectObservationBoundary
  field
    internalRouteDifferenceMeansExternalLeak : Bool
    internalRouteDifferenceMeansExternalLeakIsFalse :
      internalRouteDifferenceMeansExternalLeak ≡ false
    directFlagReturnPermittedByFIPS203 : Bool
    directFlagReturnPermittedByFIPS203IsFalse :
      directFlagReturnPermittedByFIPS203 ≡ false
    downstreamSplitNeedsSeparateWitness : Bool
    downstreamSplitNeedsSeparateWitnessIsTrue :
      downstreamSplitNeedsSeparateWitness ≡ true

open ImplicitRejectObservationBoundary public

canonicalImplicitRejectObservationBoundary : ImplicitRejectObservationBoundary
canonicalImplicitRejectObservationBoundary =
  implicitRejectObservationBoundary false refl false refl true refl
