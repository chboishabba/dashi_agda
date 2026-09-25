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
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.ConsumerGuidedReopenableRefinementExact as Refine
import DASHI.Core.NonginOnePointOneArmyRefinementExact as Nongin
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.FiniteBranchingCriticalityExact as Branch
import DASHI.Core.DecimalResidualRefinementExact as Decimal
import DASHI.Core.DecimalStageResidualBarrierExact as DecimalStage
import DASHI.Promotion.MetacognitiveFrameBearingState as Meta

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


------------------------------------------------------------------------
-- 5. Existing DASHI 1.1 / +10% role separation.
--
-- The same printed token "1.1" must not identify these roles:
--
--   * physical angle: an approximately 1.1 degree experimental/theory regime;
--   * arithmetic gain: the exact rational factor 11/10;
--   * metacognitive 1.1: an added frame-bearing coordinate, not a scalar gain;
--   * decimal refinement: a fine coordinate that preserves its coarse stage.
--
-- The point of this section is a collision firewall, not numerology.
------------------------------------------------------------------------

data OnePointOneRole : Set where
  twistronicsApproximateAngleRole : OnePointOneRole
  exactTenPercentScalarRole : OnePointOneRole
  metacognitiveFrameCoordinateRole : OnePointOneRole
  decimalFineRefinementRole : OnePointOneRole

twistronicsRoleDistinctFromScalarRole :
  twistronicsApproximateAngleRole ≡ exactTenPercentScalarRole → ⊥
twistronicsRoleDistinctFromScalarRole ()

twistronicsRoleDistinctFromMetaRole :
  twistronicsApproximateAngleRole ≡ metacognitiveFrameCoordinateRole → ⊥
twistronicsRoleDistinctFromMetaRole ()

scalarRoleDistinctFromMetaRole :
  exactTenPercentScalarRole ≡ metacognitiveFrameCoordinateRole → ⊥
scalarRoleDistinctFromMetaRole ()

decimalFineRoleDistinctFromTwistronicsRole :
  decimalFineRefinementRole ≡ twistronicsApproximateAngleRole → ⊥
decimalFineRoleDistinctFromTwistronicsRole ()

-- Reuse the already-proved exact +10% arithmetic.  No new calculation is
-- introduced here.
threeAxisExactTenPercentGainNumerator :
  Branch.pow 11 3 ≡ 1331
threeAxisExactTenPercentGainNumerator =
  Branch.threeAxisTenPercentGainNumerator

threeAxisExactTenPercentGainDenominator :
  Branch.pow 10 3 ≡ 1000
threeAxisExactTenPercentGainDenominator =
  Branch.threeAxisTenPercentGainDenominator

-- Reuse the existing theorem that decimal fine refinement does not itself move
-- the coarse stage.
decimalFineDepthPreservesCoarseStage :
  (digit : Decimal.DecimalDigit) →
  (depth : Nat) →
  DecimalStage.refinedStage digit depth ≡ DecimalStage.digitStage digit
decimalFineDepthPreservesCoarseStage =
  DecimalStage.refinementDepthPreservesCoarseStage

-- Reuse the existing metacognitive boundary rather than reinterpret 1.1 as a
-- scalar increase in information.
metacognitiveOnePointOneIsNotLiteralTenPercentGain :
  Meta.MetacognitivePowerUpBoundary.literalTenPercentKnowledgeGainClaimed
    Meta.canonicalMetacognitivePowerUpBoundary
  ≡ false
metacognitiveOnePointOneIsNotLiteralTenPercentGain = refl

record OnePointOneCrossPollinationBoundary : Set where
  constructor one-point-one-cross-pollination-boundary
  field
    exactElevenTenthsArithmeticReused : Bool
    decimalFineStageBarrierReused : Bool
    metacognitiveNonScalarBoundaryReused : Bool
    approximateMagicAngleEqualsExactElevenTenths : Bool
    equalPrintedTokenImpliesEqualRole : Bool
    exactTenPercentGainExplainsMagicAnglePhysics : Bool
    metacognitiveOnePointOneExplainsMagicAnglePhysics : Bool
    decimalRefinementExplainsMagicAnglePhysics : Bool

canonicalOnePointOneCrossPollinationBoundary :
  OnePointOneCrossPollinationBoundary
canonicalOnePointOneCrossPollinationBoundary =
  one-point-one-cross-pollination-boundary
    true true true
    false false false false false


------------------------------------------------------------------------
-- 6. Registration as an exact strict refinement of the microscopic pair.
--
-- The coarse observer remembers only the two microscopic sheets.  The refined
-- observer also retains relative registration.  A registration-sensitive
-- physical consumer is therefore an exact witness that the coarse pair alone
-- is insufficient for that consumer.
------------------------------------------------------------------------

MicroscopicPair : Set -> Set
MicroscopicPair Microscopic = Microscopic × Microscopic

forgetRegistration :
  {Microscopic Registration : Set} ->
  OverlayState Microscopic Registration ->
  MicroscopicPair Microscopic
forgetRegistration state =
  leftMicroscopic state , rightMicroscopic state

retainRegistration :
  {Microscopic Registration : Set} ->
  OverlayState Microscopic Registration ->
  OverlayState Microscopic Registration
retainRegistration state = state

microscopicPairFactorsThroughRegistration :
  {Microscopic Registration : Set} ->
  (state : OverlayState Microscopic Registration) ->
  forgetRegistration state
  ≡ forgetRegistration (retainRegistration state)
microscopicPairFactorsThroughRegistration state = refl

registrationSensitivityImpliesDistinctRegistrations :
  {Microscopic Registration Effective : Set} ->
  (system : RelativeRegistrationSystem Microscopic Registration Effective) ->
  (witness : RegistrationSensitiveWitness system) ->
  firstRegistration witness ≡ secondRegistration witness -> ⊥
registrationSensitivityImpliesDistinctRegistrations system witness same =
  effectiveChanges witness
    (cong
      (λ registration ->
        observeEffective system
          (overlay
            (microscopic witness)
            (microscopic witness)
            registration))
      same)

registrationStrictlyRefinesMicroscopicPair :
  {Microscopic Registration Effective : Set} ->
  (system : RelativeRegistrationSystem Microscopic Registration Effective) ->
  (witness : RegistrationSensitiveWitness system) ->
  Refine.StrictProjectionRefinement
    forgetRegistration
    retainRegistration
registrationStrictlyRefinesMicroscopicPair system witness =
  Refine.strictProjectionRefinement
    forgetRegistration
    microscopicPairFactorsThroughRegistration
    (overlay
      (microscopic witness)
      (microscopic witness)
      (firstRegistration witness))
    (overlay
      (microscopic witness)
      (microscopic witness)
      (secondRegistration witness))
    refl
    (λ same ->
      registrationSensitivityImpliesDistinctRegistrations
        system witness
        (cong relativeRegistration same))

registrationConsumerGuidedRefinement :
  {Microscopic Registration Effective : Set} ->
  (system : RelativeRegistrationSystem Microscopic Registration Effective) ->
  (witness : RegistrationSensitiveWitness system) ->
  Refine.ConsumerGuidedRefinement
    forgetRegistration
    retainRegistration
    (observeEffective system)
registrationConsumerGuidedRefinement system witness =
  Refine.consumerGuidedRefinement
    (registrationStrictlyRefinesMicroscopicPair system witness)
    (effectiveChanges witness)

coarseMicroscopicPairCannotServeRegistrationSensitiveConsumer :
  {Microscopic Registration Effective : Set} ->
  (system : RelativeRegistrationSystem Microscopic Registration Effective) ->
  (witness : RegistrationSensitiveWitness system) ->
  Base.ConsumerDescent
    forgetRegistration
    (observeEffective system) ->
  ⊥
coarseMicroscopicPairCannotServeRegistrationSensitiveConsumer system witness =
  Refine.consumerGuidedRefinementRefutesOldDescent
    (registrationConsumerGuidedRefinement system witness)

------------------------------------------------------------------------
-- 7. Nongin / twistronics common abstraction boundary.
--
-- Both lanes instantiate strict refinement of a coarse observer by retaining a
-- coordinate that a declared consumer can distinguish.  That common theorem
-- shape does NOT identify the coordinates, mechanisms, semantics, or domains.
------------------------------------------------------------------------

record NonginTwistronicsRefinementBoundary : Set where
  constructor nongin-twistronics-refinement-boundary
  field
    nonginUsesStrictProjectionRefinement : Bool
    twistronicsUsesStrictProjectionRefinement : Bool
    bothRequireConsumerSeparationWitness : Bool
    sharedTheoremShapeImpliesSharedMechanism : Bool
    frameCoordinateIsTwistAngle : Bool
    cognitiveConsumerIsElectronicHamiltonian : Bool
    onePointOneNotationExplainsMagicAngleValue : Bool

canonicalNonginTwistronicsRefinementBoundary :
  NonginTwistronicsRefinementBoundary
canonicalNonginTwistronicsRefinementBoundary =
  nongin-twistronics-refinement-boundary
    true true true
    false false false false

nonginCanonicalRefinementRetained :
  Refine.ConsumerGuidedRefinement
    (Nongin.onePointZeroProject {Nongin.Base1} {Nongin.Frame2})
    (Nongin.onePointOneProject {Nongin.Base1} {Nongin.Frame2})
    Nongin.frameSensitiveResponse
nonginCanonicalRefinementRetained =
  Nongin.canonicalOnePointOneRefinement
