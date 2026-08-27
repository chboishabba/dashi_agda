module DASHI.Core.FormalClaimTransportGeometryExact where

------------------------------------------------------------------------
-- FORMAL CLAIM TRANSPORT GEOMETRY
--
-- Generic owner for a pattern repeated across DASHI:
--
--   representation / projection / translation
--       + explicitly named preservation law
--       -> licensed transport of one declared consumer / claim.
--
-- The important negative theorem is equally generic: a pair of source states
-- identified by the representation but separated by the claim blocks any such
-- factorization.  This is the same fibre/non-descent mechanism already owned by
-- ConsumerDescentMinimalObserverExact; this module reuses that owner instead of
-- defining another quotient calculus.
--
-- The interpretation is intentionally broad.  `State` can be a physical state,
-- proof term, historical reconstruction state, semantic state, or any other
-- carrier.  `representation` is what is retained.  `claim` is the conclusion
-- whose transport is being requested.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized

------------------------------------------------------------------------
-- A claim is transportable through a representation exactly when it factors
-- through that representation.
------------------------------------------------------------------------

ClaimFactorsThrough :
  ∀ {State Representation Claim : Set} →
  (State → Representation) →
  (State → Claim) → Set₁
ClaimFactorsThrough representation claim =
  Descent.FactorsThrough representation claim

record ClaimTransport
    {State Representation Claim : Set}
    (representation : State → Representation)
    (claim : State → Claim) : Set₁ where
  constructor claimTransport
  field
    factor : Representation → Claim
    transportLaw :
      (state : State) →
      claim state ≡ factor (representation state)

open ClaimTransport public

toFactorizedRefinement :
  ∀ {State Representation Claim : Set}
    {representation : State → Representation}
    {claim : State → Claim} →
  ClaimTransport representation claim →
  ClaimFactorsThrough representation claim
toFactorizedRefinement transport =
  Factorized.factorizedRefinement
    (factor transport)
    (transportLaw transport)

fromFactorizedRefinement :
  ∀ {State Representation Claim : Set}
    {representation : State → Representation}
    {claim : State → Claim} →
  ClaimFactorsThrough representation claim →
  ClaimTransport representation claim
fromFactorizedRefinement refinement =
  claimTransport
    (Factorized.factor refinement)
    (Factorized.factorizes refinement)

identityClaimTransport :
  ∀ {State Value : Set}
    (observe : State → Value) →
  ClaimTransport observe observe
identityClaimTransport observe =
  claimTransport (λ value → value) (λ state → refl)

------------------------------------------------------------------------
-- Claim transport composes.  This is the generic commuting-square stack used
-- in representation, simulation, proof translation and semantic projection.
------------------------------------------------------------------------

composeClaimTransport :
  ∀ {State Fine Middle Claim : Set}
    {fine : State → Fine}
    {middle : State → Middle}
    {claim : State → Claim} →
  ClaimTransport middle claim →
  ClaimTransport fine middle →
  ClaimTransport fine claim
composeClaimTransport first second =
  fromFactorizedRefinement
    (Factorized.composeFactorizedRefinement
      (toFactorizedRefinement first)
      (toFactorizedRefinement second))

------------------------------------------------------------------------
-- Anti-promotion / non-descent witness.
------------------------------------------------------------------------

ClaimNonTransportWitness :
  ∀ {State Representation Claim : Set} →
  (State → Representation) →
  (State → Claim) → Set
ClaimNonTransportWitness representation claim =
  Descent.ConsumerNonDescentWitness representation claim

claimNonTransportWitnessBlocksTransport :
  ∀ {State Representation Claim : Set}
    {representation : State → Representation}
    {claim : State → Claim} →
  ClaimNonTransportWitness representation claim →
  ClaimTransport representation claim →
  ⊥
claimNonTransportWitnessBlocksTransport witness transport =
  Descent.nonDescentWitnessBlocksFactorization witness
    (toFactorizedRefinement transport)

------------------------------------------------------------------------
-- Explicit preservation packages.
--
-- A map existing is not enough.  The preservation datum names which structure
-- is actually known to commute with the map.  Different consumers can require
-- different packages even over the same representation.
------------------------------------------------------------------------

record StructurePreservingClaimTransport
    {State Representation Structure Claim : Set}
    (representation : State → Representation)
    (structure : State → Structure)
    (claim : State → Claim) : Set₁ where
  constructor structurePreservingClaimTransport
  field
    structureTransport : ClaimTransport representation structure
    claimTransportFromStructure : ClaimTransport structure claim

open StructurePreservingClaimTransport public

structurePackageYieldsClaimTransport :
  ∀ {State Representation Structure Claim : Set}
    {representation : State → Representation}
    {structure : State → Structure}
    {claim : State → Claim} →
  StructurePreservingClaimTransport representation structure claim →
  ClaimTransport representation claim
structurePackageYieldsClaimTransport package =
  composeClaimTransport
    (claimTransportFromStructure package)
    (structureTransport package)

------------------------------------------------------------------------
-- Comparison axes are intentionally independent labels.  They are useful for
-- auditing which bridge a project has actually discharged without pretending
-- that the labels form a total order.
------------------------------------------------------------------------

data ComparisonAxis : Set where
  historicalFidelity : ComparisonAxis
  representationFidelity : ComparisonAxis
  derivationalFidelity : ComparisonAxis
  proofTranslationStrength : ComparisonAxis
  contradictionPreservation : ComparisonAxis
  interpretability : ComparisonAxis
  conservativity : ComparisonAxis
  relativeCompleteness : ComparisonAxis
  semanticSoundness : ComparisonAxis
  semanticCompleteness : ComparisonAxis
  reflectionStrength : ComparisonAxis
  metatheoreticConclusion : ComparisonAxis

record ComparisonStrengthProfile : Set₁ where
  constructor comparisonStrengthProfile
  field
    Supports : ComparisonAxis → Set

open ComparisonStrengthProfile public

------------------------------------------------------------------------
-- Boundary: the generic theorem licenses only explicitly factorized claims.
------------------------------------------------------------------------

record FormalClaimTransportGeometryBoundary : Set where
  constructor formalClaimTransportGeometryBoundary
  field
    claimTransportIsFactorization : Bool
    claimTransportIsFactorizationIsTrue :
      claimTransportIsFactorization ≡ true

    transportCompositionAvailable : Bool
    transportCompositionAvailableIsTrue :
      transportCompositionAvailable ≡ true

    nonDescentWitnessBlocksTransport : Bool
    nonDescentWitnessBlocksTransportIsTrue :
      nonDescentWitnessBlocksTransport ≡ true

    comparisonAxesAreDefinitionallyTotallyOrdered : Bool
    comparisonAxesAreDefinitionallyTotallyOrderedIsFalse :
      comparisonAxesAreDefinitionallyTotallyOrdered ≡ false

    existenceOfRepresentationMapTransportsEveryClaim : Bool
    existenceOfRepresentationMapTransportsEveryClaimIsFalse :
      existenceOfRepresentationMapTransportsEveryClaim ≡ false

canonicalFormalClaimTransportGeometryBoundary :
  FormalClaimTransportGeometryBoundary
canonicalFormalClaimTransportGeometryBoundary =
  formalClaimTransportGeometryBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
