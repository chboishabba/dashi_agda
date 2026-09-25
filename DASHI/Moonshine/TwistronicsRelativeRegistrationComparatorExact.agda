module DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact where

------------------------------------------------------------------------
-- TWISTRONICS RELATIVE-REGISTRATION COMPARATOR
--
-- ATTRIBUTION / PROMOTION FIREWALL
--
-- External physics:
--   * Rafi Bistritzer / Allan H. MacDonald (2011):
--       moire bands and magic-angle flattening in the continuum model.
--   * Yuan Cao et al. (2018):
--       correlated insulating behaviour and superconductivity in
--       magic-angle twisted bilayer graphene.
--
-- DASHI contribution:
--   the generic typed abstraction
--
--     same microscopic carrier + relative registration
--       -> effective observer/carrier
--
--   and the proof that a change of relative registration can change an
--   effective observation while the two microscopic slots retain the same
--   carrier type.
--
-- This module DOES NOT identify a moire cell with SSP15, Base369, a
-- j-invariant fibre, an Ogg lane, or any other DASHI object.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attribution

------------------------------------------------------------------------
-- 1. External-source atlas.
------------------------------------------------------------------------

bistritzerMacDonald2011 : Attribution.AttributedSource
bistritzerMacDonald2011 =
  Attribution.mkDOISource
    "Rafi Bistritzer and Allan H. MacDonald"
    "Moiré bands in twisted double-layer graphene"
    "Proceedings of the National Academy of Sciences 108(30), 12233-12237"
    "2011"
    "10.1073/pnas.1108174108"
    "https://doi.org/10.1073/pnas.1108174108"
    Attribution.academicArticleSource
    "source for the continuum-model moire-band construction and discrete magic angles at which the low-energy band flattens; does not state any DASHI codec, fibre, SSP15, 369, or j-invariant theorem"
    Attribution.publicAttribution

caoCorrelatedInsulator2018 : Attribution.AttributedSource
caoCorrelatedInsulator2018 =
  Attribution.mkDOISource
    "Yuan Cao et al."
    "Correlated insulator behaviour at half-filling in magic-angle graphene superlattices"
    "Nature 556, 80-84"
    "2018"
    "10.1038/nature26154"
    "https://doi.org/10.1038/nature26154"
    Attribution.academicArticleSource
    "experimental source for correlated insulating behaviour in magic-angle twisted bilayer graphene; does not state the DASHI relative-registration abstraction"
    Attribution.publicAttribution

caoSuperconductivity2018 : Attribution.AttributedSource
caoSuperconductivity2018 =
  Attribution.mkDOISource
    "Yuan Cao et al."
    "Unconventional superconductivity in magic-angle graphene superlattices"
    "Nature 556, 43-50"
    "2018"
    "10.1038/nature26160"
    "https://doi.org/10.1038/nature26160"
    Attribution.academicArticleSource
    "experimental source for gate-tunable superconductivity near the first magic angle; does not state any DASHI recognition or same-object claim"
    Attribution.publicAttribution

twistronicsSourceAtlas : Attribution.AttributedSourceAtlas
twistronicsSourceAtlas =
  Attribution.mkSourceAtlas
    "Twisted-bilayer graphene relative-registration comparator source atlas"
    "DASHI.Moonshine.TwistronicsRelativeRegistrationComparatorExact"
    (bistritzerMacDonald2011 ∷
     caoCorrelatedInsulator2018 ∷
     caoSuperconductivity2018 ∷ [])
    "external sources establish the graphene/twistronics facts; the relative-registration carrier abstraction and all cross-domain comparison statements are repository constructions"

------------------------------------------------------------------------
-- 2. Claim-origin separation.
------------------------------------------------------------------------

data ClaimOrigin : Set where
  externalTwistronicsTheory : ClaimOrigin
  externalTwistronicsExperiment : ClaimOrigin
  repositoryFormalAbstraction : ClaimOrigin
  repositoryCrossDomainComparator : ClaimOrigin
  forbiddenSameObjectPromotion : ClaimOrigin

moireMagicAngleOrigin : ClaimOrigin
moireMagicAngleOrigin = externalTwistronicsTheory

correlatedPhaseOrigin : ClaimOrigin
correlatedPhaseOrigin = externalTwistronicsExperiment

relativeRegistrationAbstractionOrigin : ClaimOrigin
relativeRegistrationAbstractionOrigin = repositoryFormalAbstraction

codecFibreComparatorOrigin : ClaimOrigin
codecFibreComparatorOrigin = repositoryCrossDomainComparator

------------------------------------------------------------------------
-- 3. Generic relative-registration carrier.
------------------------------------------------------------------------

record OverlayState (Microscopic Registration : Set) : Set where
  constructor overlay
  field
    leftMicroscopic : Microscopic
    rightMicroscopic : Microscopic
    relativeRegistration : Registration

open OverlayState public

record RelativeRegistrationSystem
    (Microscopic Registration Effective : Set) : Set₁ where
  constructor relative-registration-system
  field
    observeEffective :
      OverlayState Microscopic Registration -> Effective

open RelativeRegistrationSystem public

sameMicroscopicSlots :
  {Microscopic Registration : Set} ->
  OverlayState Microscopic Registration ->
  Set
sameMicroscopicSlots {Microscopic} _ = Microscopic

changeRegistration :
  {Microscopic Registration : Set} ->
  OverlayState Microscopic Registration ->
  Registration ->
  OverlayState Microscopic Registration
changeRegistration state registration =
  overlay
    (leftMicroscopic state)
    (rightMicroscopic state)
    registration

changeRegistrationPreservesLeft :
  {Microscopic Registration : Set} ->
  (state : OverlayState Microscopic Registration) ->
  (registration : Registration) ->
  leftMicroscopic (changeRegistration state registration)
  ≡ leftMicroscopic state
changeRegistrationPreservesLeft state registration = refl

changeRegistrationPreservesRight :
  {Microscopic Registration : Set} ->
  (state : OverlayState Microscopic Registration) ->
  (registration : Registration) ->
  rightMicroscopic (changeRegistration state registration)
  ≡ rightMicroscopic state
changeRegistrationPreservesRight state registration = refl

record RegistrationSensitiveWitness
    {Microscopic Registration Effective : Set}
    (system :
      RelativeRegistrationSystem Microscopic Registration Effective) : Set where
  constructor registration-sensitive-witness
  field
    microscopic : Microscopic
    firstRegistration : Registration
    secondRegistration : Registration
    effectiveChanges :
      observeEffective system
        (overlay microscopic microscopic firstRegistration)
      ≢
      observeEffective system
        (overlay microscopic microscopic secondRegistration)

open RegistrationSensitiveWitness public

relativeRegistrationCanChangeEffectiveObservation :
  {Microscopic Registration Effective : Set} ->
  (system :
    RelativeRegistrationSystem Microscopic Registration Effective) ->
  RegistrationSensitiveWitness system ->
  Set
relativeRegistrationCanChangeEffectiveObservation system witness =
  observeEffective system
    (overlay
      (microscopic witness)
      (microscopic witness)
      (firstRegistration witness))
  ≢
  observeEffective system
    (overlay
      (microscopic witness)
      (microscopic witness)
      (secondRegistration witness))

relativeRegistrationCanChangeEffectiveObservation
  system witness = effectiveChanges witness

------------------------------------------------------------------------
-- 4. Comparator semantics.
--
-- The only cross-domain statement promoted here is structural:
--
--   a relative-registration coordinate can be semantically active even when
--   the underlying microscopic carrier type is unchanged.
--
-- No physical graphene claim is transferred to the J/369/SSP15 lane.
------------------------------------------------------------------------

record TwistronicsComparatorBoundary : Set where
  constructor twistronics-comparator-boundary
  field
    primaryTheoryAttributed : Bool
    primaryExperimentsAttributed : Bool
    genericRegistrationCarrierRepositoryOwned : Bool
    registrationSensitivityRequiresWitness : Bool
    moireCellIdentifiedWithSSP15 : Bool
    twistAngleIdentifiedWithBase369Digit : Bool
    grapheneBandIdentifiedWithJInvariantFibre : Bool
    twistronicsProvesOggRecognition : Bool
    crossDomainSameObjectPromotionMade : Bool

open TwistronicsComparatorBoundary public

canonicalTwistronicsComparatorBoundary : TwistronicsComparatorBoundary
canonicalTwistronicsComparatorBoundary =
  twistronics-comparator-boundary
    true
    true
    true
    true
    false
    false
    false
    false
    false
