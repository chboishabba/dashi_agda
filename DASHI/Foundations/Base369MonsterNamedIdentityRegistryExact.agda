module DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact as Completion
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Culture.IntellectualReceptionActionVoxelGovernedSymmetryExact as ActionVoxel

------------------------------------------------------------------------
-- STABLE NAMED IDENTITY REGISTRY
--
-- Bare cardinalities are not semantic identifiers.  Every repeated number is
-- split into named carriers, and equal-cardinality carriers remain distinct
-- unless a separately named bridge is constructed.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Two distinct eight-element identities.
------------------------------------------------------------------------

data NonIdentityMode4 : Set where
  modeA2 modeB1 modeB2 modeE : NonIdentityMode4

ReducedNonary8 : Set
ReducedNonary8 = NonIdentityMode4 × Stable.Orientation2

-- Geometric corner signs of the 3x3x3 ternary voxel.
data OuterSign2 : Set where
  negativeOuter positiveOuter : OuterSign2

record Corner8 : Set where
  constructor corner8
  field
    xSign : OuterSign2
    ySign : OuterSign2
    zSign : OuterSign2

open Corner8 public

reducedNonaryCount : Nat
reducedNonaryCount = 8

cornerCarrierCount : Nat
cornerCarrierCount = 8

cornerCountAgreesWithExistingStratum :
  cornerCarrierCount ≡ Strata.cornerCount
cornerCountAgreesWithExistingStratum = refl

------------------------------------------------------------------------
-- 2. Stable mode-boundary identities from the existing 54 -> 53 lane.
------------------------------------------------------------------------

ModeNonary45 : Set
ModeNonary45 = Stable.FiveMode × Stable.Nonary9

-- Distinguished nonary sector before removal of one invariant/identity mode.
DistinguishedNonary9 : Set
DistinguishedNonary9 = Stable.Nonary9

-- Full local Moonshine boundary: 45 ordinary mode/nonary states plus one full
-- distinguished nonary sector.
ModeBoundary54 : Set
ModeBoundary54 = ModeNonary45 ⊎ DistinguishedNonary9

-- Reduced local boundary: the distinguished nonary sector has been replaced
-- by its named nonidentity eight-state residual.
ModeBoundary53 : Set
ModeBoundary53 = ModeNonary45 ⊎ ReducedNonary8

------------------------------------------------------------------------
-- 3. Do not collapse the two 54s.
------------------------------------------------------------------------

SituatedCompletion54 : Set
SituatedCompletion54 = Stable.Completion54

-- These two carriers both have cardinality 54, but have different constructors
-- and different roles.  No bridge is supplied here.
data Situated54EqualsModeBoundary54 : Set where

theTwoFiftyFoursAreNotIdentifiedByCardinality :
  Situated54EqualsModeBoundary54 → ⊥
theTwoFiftyFoursAreNotIdentifiedByCardinality ()

------------------------------------------------------------------------
-- 4. Decision 27 with stable semantic coordinate names.
--
-- This follows the already merged action-voxel role assignment:
--   x = comparison outcome
--   y = response policy
--   z = independent-authority status.
--
-- The values are retained as ternary codes here, while the richer action owner
-- continues to own response/authority-specific semantic constructors.
------------------------------------------------------------------------

record DecisionCondition27 : Set where
  constructor decision-condition-27
  field
    comparisonOutcome : Base.TriTruth
    responsePolicy : Base.TriTruth
    independentAuthority : Base.TriTruth

open DecisionCondition27 public

base27ToDecision : Stable.Base27 → DecisionCondition27
base27ToDecision (Stable.base27 comparison response authority) =
  decision-condition-27 comparison response authority

decisionToBase27 : DecisionCondition27 → Stable.Base27
decisionToBase27
  (decision-condition-27 comparison response authority) =
  Stable.base27 comparison response authority

decisionBaseRoundTrip :
  (state : Stable.Base27) → decisionToBase27 (base27ToDecision state) ≡ state
decisionBaseRoundTrip (Stable.base27 comparison response authority) = refl

baseDecisionRoundTrip :
  (state : DecisionCondition27) → base27ToDecision (decisionToBase27 state) ≡ state
baseDecisionRoundTrip (decision-condition-27 comparison response authority) = refl

decision27IsBase27 : Stable.CarrierIso Stable.Base27 DecisionCondition27
decision27IsBase27 =
  Stable.carrier-iso
    base27ToDecision
    decisionToBase27
    decisionBaseRoundTrip
    baseDecisionRoundTrip

------------------------------------------------------------------------
-- 5. Named semantic Monster bulk.
--
-- A state now says explicitly which stable thing each coordinate means:
--   mode identity       : one of the five D4 mode labels;
--   situated perspective: observational/actionability vs governed/provenance;
--   decision condition  : comparison / response / authority ternary state;
--   appraisal state     : six named situated ternary coordinates.
------------------------------------------------------------------------

record NamedMonsterDecisionState196830 : Set where
  constructor named-monster-decision-state
  field
    modeIdentity : Stable.FiveMode
    situatedPerspective : Completion.SituatedTriadRow
    decisionCondition : DecisionCondition27
    appraisalState : Stable.Appraisal729

open NamedMonsterDecisionState196830 public

five54AppraisalToNamed :
  Stable.BulkFive54Appraisal → NamedMonsterDecisionState196830
five54AppraisalToNamed (mode , completion , appraisal) with
  Stable.completion54ToTwoBy27 completion
... | row , state27 =
  named-monster-decision-state
    mode row (base27ToDecision state27) appraisal

namedToFive54Appraisal :
  NamedMonsterDecisionState196830 → Stable.BulkFive54Appraisal
namedToFive54Appraisal
  (named-monster-decision-state mode row decision appraisal) =
  mode ,
  Stable.completion54FromTwoBy27 (row , decisionToBase27 decision) ,
  appraisal

five54NamedRoundTrip :
  (state : Stable.BulkFive54Appraisal) →
  namedToFive54Appraisal (five54AppraisalToNamed state) ≡ state
five54NamedRoundTrip (mode , completion , appraisal) with
  Stable.completion54ToTwoBy27 completion
... | row , state27
  rewrite Stable.completion54ToFrom (row , state27) = refl

namedFive54RoundTrip :
  (state : NamedMonsterDecisionState196830) →
  five54AppraisalToNamed (namedToFive54Appraisal state) ≡ state
namedFive54RoundTrip
  (named-monster-decision-state mode row decision appraisal)
  rewrite baseDecisionRoundTrip decision = refl

namedMonsterDecisionIso :
  Stable.CarrierIso
    Stable.BulkFive54Appraisal
    NamedMonsterDecisionState196830
namedMonsterDecisionIso =
  Stable.carrier-iso
    five54AppraisalToNamed
    namedToFive54Appraisal
    five54NamedRoundTrip
    namedFive54RoundTrip

------------------------------------------------------------------------
-- 6. Registry tags prevent accidental numeric substitution.
------------------------------------------------------------------------

data StableIdentityTag : Set where
  identity2Orientation
  identity3Ternary
  identity4NontrivialModes
  identity5Modes
  identity6SituatedSlots
  identity8ReducedNonary
  identity8VoxelCorners
  identity9ComparisonNonary
  identity10PointedNonary
  identity12VoxelEdges
  identity27DecisionCondition
  identity45ModeNonary
  identity53ReducedModeBoundary
  identity54SituatedCompletion
  identity54ModeBoundary
  identity729SituatedAppraisal
  identity19683FineDecisionAppraisal
  identity196830NamedMonsterDecisionSpace
  : StableIdentityTag

------------------------------------------------------------------------
-- 7. Stable meaning receipt.
------------------------------------------------------------------------

record NamedMonsterMeaningBoundary : Set where
  constructor named-monster-meaning-boundary
  field
    eightMeansFaces : Bool
    eightCornerCarrierNamed : Bool
    reducedEightCarrierNamedSeparately : Bool
    sameCardinalityEightMeansSameCarrier : Bool
    twoDifferentFiftyFourCarriersNamed : Bool
    sameCardinalityFiftyFourMeansSameCarrier : Bool
    decisionTwentySevenHasTypedRoles : Bool
    named196830StateConstructed : Bool
    geometricSymmetryMayShuffleSemanticRolesFreely : Bool
    namedCarrierAloneConstructsMonsterGroupAction : Bool

canonicalNamedMonsterMeaningBoundary : NamedMonsterMeaningBoundary
canonicalNamedMonsterMeaningBoundary =
  named-monster-meaning-boundary
    false true true false true false true true false false

-- Existing richer semantic authority remains external to the registry.
actionVoxelBoundaryRetained :
  ActionVoxel.IntellectualReceptionActionVoxelGovernedSymmetryBoundary
actionVoxelBoundaryRetained =
  ActionVoxel.canonicalIntellectualReceptionActionVoxelGovernedSymmetryBoundary
