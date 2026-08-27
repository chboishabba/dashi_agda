module DASHI.Core.IrigarayLabialRelationalCarrierExact where

------------------------------------------------------------------------
-- IRIGARAY LABIAL / TWO-LIPS RELATIONAL CARRIER
--
-- PRIMARY SOURCE
--
-- Luce Irigaray, "This Sex Which Is Not One", Cornell University Press,
-- 1985 English edition. ISBN 9780801493317.
--
-- SOURCE ROLE
--
-- The primary source motivates a non-phallic morphology in which the two lips
-- remain in reciprocal contact, cannot be cleanly resolved into active versus
-- passive toucher/touched positions, and are described as "neither one nor
-- two".  DASHI formalises that phrase as a role/classification boundary, NOT as
-- a theorem about set cardinality or a universal biological ontology.
--
-- IMPORTANT ADDRESSING BOUNDARY
--
-- Irigaray does not source-number the lips as "1" and "2".  `code1/code2` and
-- `firstLocalLipAspect/secondLocalLipAspect` are DASHI-local addresses used to
-- make reciprocal contact finite and checkable.  They must not be promoted to
-- an Irigarayan ordinal ontology.
--
-- CROSS-POLLINATION
--
-- Reuse BinaryInteractionNonseparabilityExact for the exact theorem that a
-- relational response need not decompose into endpoint-only contributions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.TernaryRoleCarrierExact as Ternary
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction

------------------------------------------------------------------------
-- Ternary role interpretation.
------------------------------------------------------------------------

data IrigarayLabialRole : Set where
  neitherOneNorTwo
  firstLocalLipAspect
  secondLocalLipAspect
  : IrigarayLabialRole

irigarayLabialRole : Ternary.TernaryRoleCode → IrigarayLabialRole
irigarayLabialRole Ternary.code0 = neitherOneNorTwo
irigarayLabialRole Ternary.code1 = firstLocalLipAspect
irigarayLabialRole Ternary.code2 = secondLocalLipAspect

irigarayLabialChart : Ternary.RoleChart IrigarayLabialRole
irigarayLabialChart = Ternary.role-chart irigarayLabialRole

------------------------------------------------------------------------
-- `code0` is classification refusal, not cardinal zero.
------------------------------------------------------------------------

data ForcedUnitaryReading : Set where
  forceAsOne forceAsTwo : ForcedUnitaryReading

forcedReadingAdmitted :
  IrigarayLabialRole → ForcedUnitaryReading → Bool
forcedReadingAdmitted neitherOneNorTwo _ = false
forcedReadingAdmitted firstLocalLipAspect forceAsOne = true
forcedReadingAdmitted firstLocalLipAspect forceAsTwo = false
forcedReadingAdmitted secondLocalLipAspect forceAsOne = false
forcedReadingAdmitted secondLocalLipAspect forceAsTwo = true

neitherRejectsForcedOne :
  forcedReadingAdmitted neitherOneNorTwo forceAsOne ≡ false
neitherRejectsForcedOne = refl

neitherRejectsForcedTwo :
  forcedReadingAdmitted neitherOneNorTwo forceAsTwo ≡ false
neitherRejectsForcedTwo = refl

------------------------------------------------------------------------
-- Reciprocal contact is constitutive data.
------------------------------------------------------------------------

data LipAspect : Set where
  lipA lipB : LipAspect

data Contact : LipAspect → LipAspect → Set where
  aTouchesB : Contact lipA lipB
  bTouchesA : Contact lipB lipA

contactSymmetric :
  {left right : LipAspect} →
  Contact left right → Contact right left
contactSymmetric aTouchesB = bTouchesA
contactSymmetric bTouchesA = aTouchesB

record LabialState : Set where
  constructor labial-state
  field
    left : LipAspect
    right : LipAspect
    contact : Contact left right

open LabialState public

canonicalLabialState : LabialState
canonicalLabialState = labial-state lipA lipB aTouchesB

------------------------------------------------------------------------
-- No privileged active/passive orientation follows from contact alone.
--
-- Constructively, an arbitrary function could always choose an orientation.
-- The exact claim encoded here is instead that the same reciprocal contact
-- admits both opposite readings and those readings are distinct; therefore the
-- contact witness does not determine a unique orientation.
------------------------------------------------------------------------

data TouchOrientation : Set where
  aActiveBPassive bActiveAPassive : TouchOrientation

orientationAdmitted : Contact lipA lipB → TouchOrientation → Bool
orientationAdmitted aTouchesB aActiveBPassive = true
orientationAdmitted aTouchesB bActiveAPassive = true

bothOrientationsAdmittedA :
  orientationAdmitted aTouchesB aActiveBPassive ≡ true
bothOrientationsAdmittedA = refl

bothOrientationsAdmittedB :
  orientationAdmitted aTouchesB bActiveAPassive ≡ true
bothOrientationsAdmittedB = refl

oppositeOrientationsDistinct :
  aActiveBPassive ≡ bActiveAPassive → ⊥
oppositeOrientationsDistinct ()

record OrientationAmbiguity : Set where
  constructor orientation-ambiguity
  field
    witnessContact : Contact lipA lipB
    firstReadingAdmitted :
      orientationAdmitted witnessContact aActiveBPassive ≡ true
    secondReadingAdmitted :
      orientationAdmitted witnessContact bActiveAPassive ≡ true
    readingsDistinct : aActiveBPassive ≡ bActiveAPassive → ⊥

canonicalOrientationAmbiguity : OrientationAmbiguity
canonicalOrientationAmbiguity =
  orientation-ambiguity
    aTouchesB refl refl oppositeOrientationsDistinct

------------------------------------------------------------------------
-- Reciprocal-contact grammar on the shared ternary carrier.
--
-- Neither-state is not the center.  The positive local aspects are linked in
-- both directions; neither is sovereign.
------------------------------------------------------------------------

irigarayReciprocalEdge :
  Ternary.TernaryRoleCode → Ternary.TernaryRoleCode → Bool
irigarayReciprocalEdge Ternary.code1 Ternary.code2 = true
irigarayReciprocalEdge Ternary.code2 Ternary.code1 = true
irigarayReciprocalEdge _ _ = false

firstTouchesSecond :
  irigarayReciprocalEdge Ternary.code1 Ternary.code2 ≡ true
firstTouchesSecond = refl

secondTouchesFirst :
  irigarayReciprocalEdge Ternary.code2 Ternary.code1 ≡ true
secondTouchesFirst = refl

neitherIsNotMasterCenter :
  irigarayReciprocalEdge Ternary.code0 Ternary.code1 ≡ false
neitherIsNotMasterCenter = refl

------------------------------------------------------------------------
-- Exact endpoint-nonseparability witness.
------------------------------------------------------------------------

labialContactResponse : LipAspect → LipAspect → Nat
labialContactResponse lipA lipA = 0
labialContactResponse lipA lipB = 1
labialContactResponse lipB lipA = 1
labialContactResponse lipB lipB = 0

labialContactSurface : Interaction.BinaryNatSurface
labialContactSurface =
  Interaction.binary-nat-surface
    LipAspect LipAspect labialContactResponse
    "Irigaray two-lips finite contact regression: reciprocal off-diagonal contact."

labialRectangleObstruction :
  Interaction.RectangleObstruction labialContactSurface
labialRectangleObstruction =
  Interaction.rectangle-obstruction lipA lipB lipA lipB (λ ())

labialRankOneObstruction :
  Interaction.RankOneMinorObstruction labialContactSurface
labialRankOneObstruction =
  Interaction.rank-one-minor-obstruction lipA lipB lipA lipB (λ ())

labialStrongInteraction :
  Interaction.StrongBinaryInteractionAdmission labialContactSurface
labialStrongInteraction =
  Interaction.strong-binary-interaction-admission
    labialRectangleObstruction labialRankOneObstruction

labialContactIsNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction labialContactSurface
labialContactIsNotEndpointAdditive =
  Interaction.strongAdmissionImpliesAdditiveNonseparability
    labialStrongInteraction

------------------------------------------------------------------------
-- Boundary: the motif is not promoted to a new universal master signifier.
------------------------------------------------------------------------

record IrigarayLabialBoundary : Set where
  constructor irigaray-labial-boundary
  field
    neitherMeansCardinalityZero : Bool
    neitherMeansCardinalityZeroIsFalse : neitherMeansCardinalityZero ≡ false
    sourceNumbersLipsAsFirstAndSecond : Bool
    sourceNumbersLipsAsFirstAndSecondIsFalse :
      sourceNumbersLipsAsFirstAndSecond ≡ false
    twoLipsMeansIndependentProduct : Bool
    twoLipsMeansIndependentProductIsFalse :
      twoLipsMeansIndependentProduct ≡ false
    reciprocalContactDeterminesUniqueActivePassiveOrientation : Bool
    reciprocalContactDeterminesUniqueActivePassiveOrientationIsFalse :
      reciprocalContactDeterminesUniqueActivePassiveOrientation ≡ false
    labialMotifIsUniversalFeminineMasterSignifier : Bool
    labialMotifIsUniversalFeminineMasterSignifierIsFalse :
      labialMotifIsUniversalFeminineMasterSignifier ≡ false
    labialMorphologyIsBiologicalSexOntology : Bool
    labialMorphologyIsBiologicalSexOntologyIsFalse :
      labialMorphologyIsBiologicalSexOntology ≡ false

canonicalIrigarayLabialBoundary : IrigarayLabialBoundary
canonicalIrigarayLabialBoundary =
  irigaray-labial-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
