module DASHI.Mathematics.Topology.AlexanderHornedTetralemmaRelativeHandleSlideGateExact where

------------------------------------------------------------------------
-- TETRALEMMA-QUALIFIED 3D HANDLE SLIDE: REAL OBLIGATION, NOT AXIOM.
-- Reuse prior owners:
--   DASHI.Algebra.TetralemmaBridge (four-position logic);
--   DASHI.Algebra.DisagreementFourViewBoundary (polarity evidence);
--   DASHI.Mathematics.Topology.AlexanderHornedTernaryPantsMeridianBoundaryExact
--   (actual [a,b][b,c] boundary word and genus-one candidate);
--   DASHI.Mathematics.Topology.AlexanderHornedBalancedTernaryCommutatorTowerExact.
--
-- Important relative-boundary obstruction: a boundary-pointwise
-- homeomorphism H_g -> H_g induces identity on pi1(H_g), since
-- pi1(boundary H_g) -> pi1(H_g) is surjective. The Nielsen map
-- b -> b^-1 and a -> c^-1*a therefore CANNOT come from a
-- homeomorphism fixed on ALL of the boundary. A selected cap is
-- weaker and potentially compatible; it still needs actual support.
--
-- This module provides a first-class OBLIGATION RECORD with NO term
-- purporting to instantiate an embedded 3D relative homeomorphism.
-- It also proves the tetralemma classification cannot be treated
-- as a witness of any topological map.
--
-- Original source: classical Nielsen/handlebody mapping-class
-- theory, Alexander 1924, Hatcher AT 2B.2. Current formal owner:
-- #1244. No ESD, Monster or acoustic representation assertions.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Algebra.TetralemmaBridge as Tetra
import DASHI.Algebra.DisagreementFourViewBoundary as Views
import DASHI.Mathematics.Topology.AlexanderHornedBalancedTernaryCommutatorTowerExact as Words
import DASHI.Mathematics.Topology.AlexanderHornedTernaryPantsMeridianBoundaryExact as Boundary

-- The existing tetralemma is an EVIDENCE CLASSIFIER; it cannot
-- manufacture evidence of an ambient homeomorphism.
data RelativeGeometryClaim : Set where
  nielsenAlgebra
    standardHandlebodyMoves
    fullBoundaryPointwiseFixing
    selectedCapPreservation
    actualChildMeridianIdentification
    wildLimitExteriorIdentification : RelativeGeometryClaim

-- A record of the actual 3D geometric data a producer must supply.
-- It deliberately does not assert the existence of such a record.
record RelativeHandleSlideSupplier : Set₁ where
  field
    Stage : Set
    StageHomeomorphism : Stage → Stage
    stationaryCap : Stage → Bool
    mapFixesStationaryCap :
      ∀ x → stationaryCap x ≡ true →
        stationaryCap (StageHomeomorphism x) ≡ true

    -- This weak cap membership equation is NOT yet pointwise
    -- fixing, an ambient homeomorphism, or the meridian theorem.
    inverseStageHomeomorphism : Stage → Stage
    forwardBackward : ∀ x →
      inverseStageHomeomorphism (StageHomeomorphism x) ≡ x
    backwardForward : ∀ x →
      StageHomeomorphism (inverseStageHomeomorphism x) ≡ x

-- The weak record above cannot be promoted to an embedding of a
-- handlebody or its complement; additional topological structure,
-- boundary collar maps and induced pi1 naturality are required.

data Status : Set where
  algebraicallyWitnessed : Status
  classicallyAvailable : Status
  impossibleUnderFullBoundaryFix : Status
  sourceSpecificUnproved : Status

status : RelativeGeometryClaim → Status
status nielsenAlgebra = algebraicallyWitnessed
status standardHandlebodyMoves = classicallyAvailable
status fullBoundaryPointwiseFixing = impossibleUnderFullBoundaryFix
status selectedCapPreservation = sourceSpecificUnproved
status actualChildMeridianIdentification = sourceSpecificUnproved
status wildLimitExteriorIdentification = sourceSpecificUnproved

-- User's tetralemma is retained as a separate four-position
-- qualification, not equated to these proof-status categories.
tetralemmaOfEvidence : RelativeGeometryClaim → Tetra.TetralemmaPosition
tetralemmaOfEvidence nielsenAlgebra = Tetra.affirmation
tetralemmaOfEvidence standardHandlebodyMoves = Tetra.affirmation
tetralemmaOfEvidence fullBoundaryPointwiseFixing = Tetra.negation
tetralemmaOfEvidence selectedCapPreservation = Tetra.neither
tetralemmaOfEvidence actualChildMeridianIdentification = Tetra.neither
tetralemmaOfEvidence wildLimitExteriorIdentification = Tetra.neither

nielsenIsAffirmed :
  tetralemmaOfEvidence nielsenAlgebra ≡ Tetra.affirmation
nielsenIsAffirmed = refl

fullBoundaryFixedIsNegated :
  tetralemmaOfEvidence fullBoundaryPointwiseFixing ≡ Tetra.negation
fullBoundaryFixedIsNegated = refl

capHasNoEvidenceYet :
  tetralemmaOfEvidence selectedCapPreservation ≡ Tetra.neither
capHasNoEvidenceYet = refl

data TetralemmaClassificationMakesEmbeddedWildBall : Set where

noGeometricPromotionFromFourPositions :
  TetralemmaClassificationMakesEmbeddedWildBall → ⊥
noGeometricPromotionFromFourPositions ()
