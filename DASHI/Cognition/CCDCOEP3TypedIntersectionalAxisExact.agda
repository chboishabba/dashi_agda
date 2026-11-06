module DASHI.Cognition.CCDCOEP3TypedIntersectionalAxisExact where

------------------------------------------------------------------------
-- CCDCOE P3: NON-EXCHANGEABLE, INDEXED RACE AND SEX AXIS POSITIONS.
--
-- Reuse canonical binary interaction, intersectional constraint geometry,
-- and non-factorability. Synthetic coordinates represent neither human
-- traits nor a calibrated measure of discrimination/oppression.
--
-- Cardinality equality is NOT carrier equality, source identity,
-- comparability, or authority for converting between the two axes.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; Σ; _,_; proj₁)
open import Data.Vec using (Vec; []; _∷_)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Core.IntersectionalBinaryInteractionBridgeExact as Existing
import DASHI.Core.IntersectionalConstraintGeometryExact as Geometry

data Axis : Set where
  raceAxis sexAxis : Axis

data AxisPoint : Axis → Set where
  race0 race1 : AxisPoint raceAxis
  sex0 sex1 : AxisPoint sexAxis

-- Both chosen finite *coordinate sets* have two values, but the values
-- are indexed by different axes and cannot be exchanged automatically.
racePoints : Vec (AxisPoint raceAxis) 2
racePoints = race0 ∷ race1 ∷ []

sexPoints : Vec (AxisPoint sexAxis) 2
sexPoints = sex0 ∷ sex1 ∷ []

axisTagsDiffer : raceAxis ≡ sexAxis → ⊥
axisTagsDiffer ()

noEvidenceForRaceSexAxisIdentification :
  Σ Axis (λ a → AxisPoint a) →
  raceAxis ≡ sexAxis → ⊥
noEvidenceForRaceSexAxisIdentification _ =
  axisTagsDiffer

-- A sum-of-carriers representation must retain the axis tag. No
-- 'two of one axis = two of the other axis' implicit coercion exists.
TaggedPoint : Set
TaggedPoint = Σ Axis (λ a → AxisPoint a)

tagRace0 tagRace1 tagSex0 tagSex1 : TaggedPoint
tagRace0 = raceAxis , race0
tagRace1 = raceAxis , race1
tagSex0 = sexAxis , sex0
tagSex1 = sexAxis , sex1

raceAndSexTagsNeverEqual :
  (r : AxisPoint raceAxis) →
  (s : AxisPoint sexAxis) →
  (raceAxis , r) ≡ (sexAxis , s) → ⊥
raceAndSexTagsNeverEqual r s eq =
  axisTagsDiffer (congTag eq)
  where
    congTag : ∀ {u v : TaggedPoint} → u ≡ v → proj₁ u ≡ proj₁ v
    congTag refl = refl

-- A response is a genuinely heterogeneous typed surface:
-- RacePosition × SexPosition → Code, not (Nat × Nat) → Code.
-- There is no common 'axis point' used as an interchangeable input.
typedJointCode :
  AxisPoint raceAxis → AxisPoint sexAxis → Nat
typedJointCode race0 sex0 = 0
typedJointCode race0 sex1 = 0
typedJointCode race1 sex0 = 0
typedJointCode race1 sex1 = 1

typedJointSurface : Interaction.BinaryNatSurface
typedJointSurface =
  Interaction.binary-nat-surface
    (AxisPoint raceAxis)
    (AxisPoint sexAxis)
    typedJointCode
    "Finite typed interaction only, not a population score"

-- The ORIGINAL generic theorem owner proves no decomposition into
-- independent endpoint potentials for this selected finite specimen.
typedRectangleObstruction :
  Interaction.RectangleObstruction typedJointSurface
typedRectangleObstruction =
  Interaction.rectangle-obstruction
    race0 race1 sex0 sex1
    (λ ())

typedJointNotAdditivelySeparable :
  Interaction.NonseparableAdditiveInteraction typedJointSurface
typedJointNotAdditivelySeparable =
  Interaction.rectangleObstructionBlocksEndpointSeparation
    typedRectangleObstruction

-- The actual original intersectionality admission is retained;
-- no second theorem is invented for the canonical marginal model.
originalIntersectionalAdmission :
  Existing.IntersectionalInteractionAdmission
originalIntersectionalAdmission =
  Existing.canonicalIntersectionalInteractionAdmission

originalJointRecognitionNotMarginalConjunction :
  Geometry.marginalPublicRecognition Geometry.jointAxes
  ≡ Geometry.interactionPublicRecognition Geometry.jointAxes → ⊥
originalJointRecognitionNotMarginalConjunction =
  Geometry.jointInteractionIsNotRecoveredByMarginalConjunction

-- Equal coordinates can still inhabit two different situated histories.
-- The point pair is a lossy observer, even when BOTH axes are retained.
data Context : Set where
  accessibleGovernance exclusionaryGovernance : Context

record Situated : Set where
  constructor situated
  field
    racePosition : AxisPoint raceAxis
    sexPosition : AxisPoint sexAxis
    context : Context

open Situated public

sameCoordinatesAccessible : Situated
sameCoordinatesAccessible =
  situated race1 sex1 accessibleGovernance

sameCoordinatesExclusionary : Situated
sameCoordinatesExclusionary =
  situated race1 sex1 exclusionaryGovernance

coordinatesOnly :
  Situated → (AxisPoint raceAxis × AxisPoint sexAxis)
coordinatesOnly world =
  racePosition world , sexPosition world

data RecognitionOutcome : Set where
  recognised excluded : RecognitionOutcome

recognition : Situated → RecognitionOutcome
recognition (situated _ _ accessibleGovernance) = recognised
recognition (situated _ _ exclusionaryGovernance) = excluded

situatedRecognitionDiffers :
  recognition sameCoordinatesAccessible
  ≡ recognition sameCoordinatesExclusionary → ⊥
situatedRecognitionDiffers ()

coordinateOnlyNonfactorability :
  NF.NonFactorabilityWitness coordinatesOnly recognition
coordinateOnlyNonfactorability =
  NF.nonFactorabilityWitness
    sameCoordinatesAccessible sameCoordinatesExclusionary
    refl situatedRecognitionDiffers

jointPositionsStillDoNotRecoverContextualOutcome :
  NF.FactorsThrough coordinatesOnly recognition → ⊥
jointPositionsStillDoNotRecoverContextualOutcome =
  NF.witnessRulesOutEveryFlatFactorisation
    coordinateOnlyNonfactorability

-- A reweighted sum, machine embedding or policy chart built ONLY
-- from the colliding pair cannot recover the missing context.
noRechartingOfCoordinatesCanRecoverRecognition :
  ∀ {Flat : Set} →
  (rechart : (AxisPoint raceAxis × AxisPoint sexAxis) → Flat) →
  NF.FactorsThrough
    (λ world → rechart (coordinatesOnly world)) recognition → ⊥
noRechartingOfCoordinatesCanRecoverRecognition rechart =
  NF.rechartingCannotRecoverErasedPhenomenon
    rechart coordinateOnlyNonfactorability
