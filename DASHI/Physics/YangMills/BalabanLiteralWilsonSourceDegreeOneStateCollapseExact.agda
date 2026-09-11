{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralWilsonSourceDegreeOneStateCollapseExact where

------------------------------------------------------------------------
-- LITERAL WILSON SOURCE DEGREE-ONE STATE COLLAPSE
--
-- The current sharp G2 route uses only the degree-one source-state norm.
-- That state is not a new physical observable:
--
--   sourceDegreeState degree1
--     = sum of the four singleton plaquette-boundary projections
--     = full plaquette-boundary projection
--     = literal Wilson first variation,
--
-- because the physical Wilson first variation is already proved to be
-- supported on the four plaquette boundary bonds.
--
-- Thus the remaining Green-side source payment is exactly a magnitude bound on
-- the literal physical Wilson first variation itself; no Möbius/preimage/KKT
-- representation theorem remains between that quantity and the G2 consumer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33FiniteKKTPseudoinverseProjectorExact as Pseudo
import DASHI.Physics.YangMills.BalabanP33PhysicalCoordinateProjectorExact as Projector
import DASHI.Physics.YangMills.BalabanP33PlaquetteBoundaryProjectorExact as Boundary
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Plaquette
import DASHI.Physics.YangMills.BalabanP33CorrelatedMobiusDegreeJointExact as Degree
import DASHI.Physics.YangMills.BalabanSelectedCanonicalConstraintAtomsFromSubsetExact as Canonical
import DASHI.Physics.YangMills.BalabanCanonicalGreenDegreeStatePreimageExact as Preimage
import DASHI.Physics.YangMills.BalabanPlaquetteSubsetMobiusDegreeOneCollapseExact as Collapse
import DASHI.Physics.YangMills.BalabanSelectedWilsonFirstVariationPlaquetteSupportExact as WilsonSource

literalWilsonSourceDegreeOneStateExact :
  ∀ {Multiplier}
    {pseudoData : Pseudo.FiniteKKTPseudoinverseData Multiplier}
    background bondField plaquette
    (inputs : Canonical.CanonicalSubsetCorrelatedAuthorityInputs
      pseudoData
      (WilsonSource.plaquetteFirstVariationCovector background plaquette)
      bondField plaquette)
    coordinate →
  Preimage.sourceDegreeState inputs Degree.degree1 coordinate
  ≡ WilsonSource.plaquetteFirstVariationCovector background plaquette coordinate
literalWilsonSourceDegreeOneStateExact
    background bondField plaquette inputs coordinate =
  trans
    (Collapse.layer1IsBoundary
      (WilsonSource.plaquetteFirstVariationCovector background plaquette)
      plaquette coordinate)
    (Projector.physicalConstraintProjectorImageCharacterizationForward
      (Boundary.plaquetteBoundaryMask plaquette)
      (WilsonSource.plaquetteFirstVariationCovector background plaquette)
      (WilsonSource.plaquetteFirstVariationSupported background plaquette)
      coordinate)

literalWilsonSourceDegreeOneStateCollapseLevel : ProofLevel
literalWilsonSourceDegreeOneStateCollapseLevel = machineChecked

-- The theorem above changes representation only.  A charge-relative estimate
-- for the norm-square of the literal Wilson first variation remains genuine
-- physical/analytic content until separately inhabited.
literalWilsonFirstVariationChargeRelativeNormLevel : ProofLevel
literalWilsonFirstVariationChargeRelativeNormLevel = conditional
