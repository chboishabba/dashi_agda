module DASHI.Core.IntersectionalBinaryInteractionBridgeExact where

------------------------------------------------------------------------
-- INTERSECTIONAL CONSTRAINT GEOMETRY -> GENERIC INTERACTION ADMISSION
--
-- PRIMARY CONCEPTUAL SOURCES
--
-- Kimberle Crenshaw,
-- "Demarginalizing the Intersection of Race and Sex: A Black Feminist
-- Critique of Antidiscrimination Doctrine, Feminist Theory and Antiracist
-- Politics", University of Chicago Legal Forum 1989(1), Article 8.
-- Stable original journal record; no DOI asserted.
--
-- Kimberle Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1241--1299 (1991).
-- DOI: 10.2307/1229039.
--
-- MATHEMATICAL OWNER
--
-- `BinaryInteractionNonseparabilityExact` owns the additive endpoint-separation
-- and rectangle-obstruction theorem.  Crenshaw supplies the conceptual reason
-- not to assume single-axis reconstruction; she is not credited with the Nat
-- response surface or rectangle algebra below.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.BinaryInteractionNonseparabilityExact as Interaction
import DASHI.Core.IntersectionalConstraintGeometryExact as Intersection

------------------------------------------------------------------------
-- A two-axis finite response code.
--
-- 0 = no extra joint interaction code in this synthetic carrier
-- 1 = a joint-only interaction code
--
-- Both single-axis marginals remain zero while the joint cell is one.  This is
-- a structural interaction witness, not a calibrated oppression score.
------------------------------------------------------------------------

data AxisPresence : Set where
  absent present : AxisPresence

intersectionInteractionCode : AxisPresence → AxisPresence → Nat
intersectionInteractionCode absent absent = 0
intersectionInteractionCode absent present = 0
intersectionInteractionCode present absent = 0
intersectionInteractionCode present present = 1

intersectionInteractionSurface : Interaction.BinaryNatSurface
intersectionInteractionSurface =
  Interaction.binary-nat-surface
    AxisPresence
    AxisPresence
    intersectionInteractionCode
    "Synthetic two-axis interaction code: both single-axis cells are zero while the joint cell is one."

intersectionRectangleObstruction :
  Interaction.RectangleObstruction intersectionInteractionSurface
intersectionRectangleObstruction =
  Interaction.rectangle-obstruction
    absent present
    absent present
    (λ ())

intersectionInteractionNotEndpointAdditive :
  Interaction.NonseparableAdditiveInteraction intersectionInteractionSurface
intersectionInteractionNotEndpointAdditive =
  Interaction.rectangleObstructionBlocksEndpointSeparation
    intersectionRectangleObstruction

------------------------------------------------------------------------
-- Link back to the existing Boolean affordance witness.
------------------------------------------------------------------------

singleHeteronormativeMarginalStillOpen :
  Intersection.interactionPublicRecognition
    Intersection.heteronormativeAxis
  ≡ true
singleHeteronormativeMarginalStillOpen = refl

singlePatriarchalMarginalStillOpen :
  Intersection.interactionPublicRecognition
    Intersection.patriarchalAxis
  ≡ true
singlePatriarchalMarginalStillOpen = refl

jointConfigurationClosesRecognition :
  Intersection.interactionPublicRecognition Intersection.jointAxes
  ≡ false
jointConfigurationClosesRecognition = refl

record IntersectionalInteractionAdmission : Set₁ where
  constructor intersectional-interaction-admission
  field
    additiveObstruction :
      Interaction.RectangleObstruction intersectionInteractionSurface
    noEndpointAdditiveReconstruction :
      Interaction.NonseparableAdditiveInteraction intersectionInteractionSurface
    leftMarginalHeldOpen :
      Intersection.interactionPublicRecognition Intersection.heteronormativeAxis
      ≡ true
    rightMarginalHeldOpen :
      Intersection.interactionPublicRecognition Intersection.patriarchalAxis
      ≡ true
    jointAffordanceClosed :
      Intersection.interactionPublicRecognition Intersection.jointAxes
      ≡ false

canonicalIntersectionalInteractionAdmission :
  IntersectionalInteractionAdmission
canonicalIntersectionalInteractionAdmission =
  intersectional-interaction-admission
    intersectionRectangleObstruction
    intersectionInteractionNotEndpointAdditive
    refl refl refl

------------------------------------------------------------------------
-- Boundary: additive nonseparability is the formal theorem; the sociological
-- interpretation remains situated and evidence-dependent.
------------------------------------------------------------------------

record IntersectionalBinaryInteractionBoundary : Set where
  constructor intersectional-binary-interaction-boundary
  field
    jointInteractionReconstructedByEndpointAdditivePotentials : Bool
    jointInteractionReconstructedByEndpointAdditivePotentialsIsFalse :
      jointInteractionReconstructedByEndpointAdditivePotentials ≡ false
    interactionCodeIsUniversalOppressionScale : Bool
    interactionCodeIsUniversalOppressionScaleIsFalse :
      interactionCodeIsUniversalOppressionScale ≡ false
    crenshawCreditedWithRectangleAlgebra : Bool
    crenshawCreditedWithRectangleAlgebraIsFalse :
      crenshawCreditedWithRectangleAlgebra ≡ false

canonicalIntersectionalBinaryInteractionBoundary :
  IntersectionalBinaryInteractionBoundary
canonicalIntersectionalBinaryInteractionBoundary =
  intersectional-binary-interaction-boundary
    false refl
    false refl
    false refl
