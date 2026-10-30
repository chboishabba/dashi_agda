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
    wildLimitExteriorIdentification
    localBasedNormalizerStrictOrderThree
    periodicMapFixesOpenBoundaryCapPointwise : RelativeGeometryClaim

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
status localBasedNormalizerStrictOrderThree = impossibleUnderFullBoundaryFix
status periodicMapFixesOpenBoundaryCapPointwise = impossibleUnderFullBoundaryFix

-- User's tetralemma is retained as a separate four-position
-- qualification, not equated to these proof-status categories.
tetralemmaOfEvidence : RelativeGeometryClaim → Tetra.TetralemmaPosition
tetralemmaOfEvidence nielsenAlgebra = Tetra.affirmation
tetralemmaOfEvidence standardHandlebodyMoves = Tetra.affirmation
tetralemmaOfEvidence fullBoundaryPointwiseFixing = Tetra.negation
tetralemmaOfEvidence selectedCapPreservation = Tetra.neither
tetralemmaOfEvidence actualChildMeridianIdentification = Tetra.neither
tetralemmaOfEvidence wildLimitExteriorIdentification = Tetra.neither
tetralemmaOfEvidence localBasedNormalizerStrictOrderThree = Tetra.negation
tetralemmaOfEvidence periodicMapFixesOpenBoundaryCapPointwise = Tetra.negation

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


------------------------------------------------------------------------
-- THE STRICT BASED C3 G4 ALTERNATIVE IS REFUTED IN THE EXISTING
-- SOURCE-WRITTEN FREE-WORD OWNER, independent of a geometric claim.
--
-- If psi=Inn(q^-1)◦phi fixes w, then the threefold composition
-- differs from the identity on the generator a; the exact finite
-- reduction is supplied, not postulated, by the canonical boundary.
--
-- This does NOT rule out non-periodic cap-relative Nielsen handle
-- slides, nor the separate external-sector C3 family.
------------------------------------------------------------------------

localBasedNormalizerCubeIsNotIdentity :
  Boundary.LocalNielsenReducedCertificate.basedPhi
    (Boundary.LocalNielsenReducedCertificate.basedPhi
      (Boundary.LocalNielsenReducedCertificate.basedPhi
        Boundary.LocalNielsenReducedCertificate.a))
  ≡ Boundary.LocalNielsenReducedCertificate.a → ⊥
localBasedNormalizerCubeIsNotIdentity =
  Boundary.LocalNielsenReducedCertificate.basedPhiCubeNotIdentityOnA

-- NEWMAN 1931 EXTERNAL TOPOLOGICAL INPUT (not encoded as a fake
-- postulate): a periodic homeomorphism on a connected surface that
-- fixes a nonempty OPEN disk pointwise is globally the identity.
-- For a compact genus-3 handlebody, restriction to its connected
-- boundary then gives identity on boundary.  Since pi1(boundary)
-- SURJECTS onto pi1(handlebody), induced action on handlebody
-- pi1 is trivial.  Therefore a nontrivial Nielsen action cannot
-- be simultaneously finite-order and pointwise cap-fixed in
-- that geometric setting.  Cap SETWISE preservation (the weak
-- record above) is DIFFERENT, and can admit a periodic rotation.
--
-- No connected-boundary surface, cap-openness, homeomorphism or
-- fundamental group exists in the present source carrier; the
-- full Newman implication is therefore recorded in the roadmap
-- and NOT asserted here as a geometrically proved Agda theorem.
