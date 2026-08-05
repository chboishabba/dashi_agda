module DASHI.Physics.YangMills.BalabanP33PhysicalFlatWilsonCurlIdentificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the rational four-link Wilson theorem on the repository's actual
-- three-component side-four positive-bond perturbation.  For a plaquette based
-- at x in the ordered axis pair mu<nu, the four tangent insertions are
--
--   h_mu(x), h_nu(x+mu), h_mu(x+nu), h_nu(x),
--
-- with the last two entering through inverse links.  The rational quaternion
-- theorem therefore gives exactly
--
--   S_p''(1)[h,h]
--     = |h_mu(x)+h_nu(x+mu)-h_mu(x+nu)-h_nu(x)|^2
--     = |d_mu h_nu(x)-d_nu h_mu(x)|^2.
--
-- Summing the six axis pairs and all 4^4 sites proves that the literal flat
-- Wilson Hessian is the physical periodic curl energy for the same h.  This is
-- the concrete flat-curvature half of the corrected Hodge comparison; no atom
-- family, norm receipt, or unrelated field is supplied by a caller.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _*_; _-_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using
  (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using
  (Axis4; pair)
import DASHI.Physics.YangMills.BalabanP33PhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Wilson
import DASHI.Physics.YangMills.BalabanP33PeriodicFourDimensionalHodgeIdentityExact as Hodge4

------------------------------------------------------------------------
-- The actual physical perturbation as a periodic scalar field in each Lie
-- coordinate and bond direction.
------------------------------------------------------------------------

asPeriodicPhysicalField :
  Physical.PhysicalSU2BondField4 → Hodge4.PhysicalBondField4
asPeriodicPhysicalField field coordinate axis site =
  field coordinate (pair site axis)

insertionAt :
  Physical.PhysicalSU2BondField4 →
  Axis4 → Hodge4.Site4 → Wilson.RationalVector3
insertionAt field axis site =
  Wilson.vec3
    (field Physical.coordinateX (pair site axis))
    (field Physical.coordinateY (pair site axis))
    (field Physical.coordinateZ (pair site axis))

flatPlaquetteSecondVariation :
  Physical.PhysicalSU2BondField4 →
  Axis4 → Axis4 → Hodge4.Site4 → ℚ
flatPlaquetteSecondVariation field left right site =
  Wilson.flatOrientedPlaquetteSecondVariation
    (insertionAt field left site)
    (insertionAt field right (Hodge4.shiftForward left site))
    (insertionAt field left (Hodge4.shiftForward right site))
    (insertionAt field right site)

plaquetteCurlCoordinate :
  Physical.PhysicalSU2BondField4 →
  Physical.LieCoordinate3 → Axis4 → Axis4 → Hodge4.Site4 → ℚ
plaquetteCurlCoordinate field coordinate left right site =
  Hodge4.curlComponent left right
    (asPeriodicPhysicalField field coordinate) site

flatPlaquetteSecondVariationIsPhysicalCurlSquare :
  ∀ field left right site →
  flatPlaquetteSecondVariation field left right site
  ≡
    plaquetteCurlCoordinate field Physical.coordinateX left right site
      * plaquetteCurlCoordinate field Physical.coordinateX left right site
    + plaquetteCurlCoordinate field Physical.coordinateY left right site
      * plaquetteCurlCoordinate field Physical.coordinateY left right site
    + plaquetteCurlCoordinate field Physical.coordinateZ left right site
      * plaquetteCurlCoordinate field Physical.coordinateZ left right site
flatPlaquetteSecondVariationIsPhysicalCurlSquare
    field left right site =
  trans
    (Wilson.flatPlaquetteWilsonIsCurlSquare
      (insertionAt field left site)
      (insertionAt field right (Hodge4.shiftForward left site))
      (insertionAt field left (Hodge4.shiftForward right site))
      (insertionAt field right site))
    (ℚRing.solve-∀
      (field Physical.coordinateX (pair site left))
      (field Physical.coordinateY (pair site left))
      (field Physical.coordinateZ (pair site left))
      (field Physical.coordinateX
        (pair (Hodge4.shiftForward left site) right))
      (field Physical.coordinateY
        (pair (Hodge4.shiftForward left site) right))
      (field Physical.coordinateZ
        (pair (Hodge4.shiftForward left site) right))
      (field Physical.coordinateX
        (pair (Hodge4.shiftForward right site) left))
      (field Physical.coordinateY
        (pair (Hodge4.shiftForward right site) left))
      (field Physical.coordinateZ
        (pair (Hodge4.shiftForward right site) left))
      (field Physical.coordinateX (pair site right))
      (field Physical.coordinateY (pair site right))
      (field Physical.coordinateZ (pair site right)))

------------------------------------------------------------------------
-- Six-pair physical sum.
------------------------------------------------------------------------

flatPlaquettePairEnergy :
  Physical.PhysicalSU2BondField4 → Axis4 → Axis4 → ℚ
flatPlaquettePairEnergy field left right =
  Hodge4.sumSites
    (flatPlaquetteSecondVariation field left right)

physicalPairCurlEnergy :
  Physical.PhysicalSU2BondField4 → Axis4 → Axis4 → ℚ
physicalPairCurlEnergy field left right =
  Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField field Physical.coordinateX))
  + Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField field Physical.coordinateY))
  + Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField field Physical.coordinateZ))

flatPlaquettePairEnergyIsPhysicalCurl : ∀ field left right →
  flatPlaquettePairEnergy field left right
  ≡ physicalPairCurlEnergy field left right
flatPlaquettePairEnergyIsPhysicalCurl field left right =
  trans
    (Hodge4.sumSitesCong _ _
      (flatPlaquetteSecondVariationIsPhysicalCurlSquare
        field left right))
    (trans
      (Hodge4.sumSitesAdd
        (λ site →
          plaquetteCurlCoordinate field Physical.coordinateX left right site
          * plaquetteCurlCoordinate field Physical.coordinateX left right site)
        (λ site →
          plaquetteCurlCoordinate field Physical.coordinateY left right site
          * plaquetteCurlCoordinate field Physical.coordinateY left right site
          + plaquetteCurlCoordinate field Physical.coordinateZ left right site
          * plaquetteCurlCoordinate field Physical.coordinateZ left right site))
      (trans
        (cong
          (Hodge4.fieldNormSq
            (Hodge4.curlComponent left right
              (asPeriodicPhysicalField field Physical.coordinateX)) +_)
          (Hodge4.sumSitesAdd
            (λ site →
              plaquetteCurlCoordinate field Physical.coordinateY left right site
              * plaquetteCurlCoordinate field Physical.coordinateY left right site)
            (λ site →
              plaquetteCurlCoordinate field Physical.coordinateZ left right site
              * plaquetteCurlCoordinate field Physical.coordinateZ left right site)))
        refl))

flatWilsonEnergy : Physical.PhysicalSU2BondField4 → ℚ
flatWilsonEnergy field =
  flatPlaquettePairEnergy field Hodge4.axis0 Hodge4.axis1
  + flatPlaquettePairEnergy field Hodge4.axis0 Hodge4.axis2
  + flatPlaquettePairEnergy field Hodge4.axis0 Hodge4.axis3
  + flatPlaquettePairEnergy field Hodge4.axis1 Hodge4.axis2
  + flatPlaquettePairEnergy field Hodge4.axis1 Hodge4.axis3
  + flatPlaquettePairEnergy field Hodge4.axis2 Hodge4.axis3

flatWilsonEnergyIsPhysicalPeriodicCurl : ∀ field →
  flatWilsonEnergy field
  ≡ Hodge4.physicalPeriodicCurlEnergy (asPeriodicPhysicalField field)
flatWilsonEnergyIsPhysicalPeriodicCurl field
  rewrite flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis0 Hodge4.axis1
  | flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis0 Hodge4.axis2
  | flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis0 Hodge4.axis3
  | flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis1 Hodge4.axis2
  | flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis1 Hodge4.axis3
  | flatPlaquettePairEnergyIsPhysicalCurl
    field Hodge4.axis2 Hodge4.axis3 =
  ℚRing.solve-∀
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField field Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField field Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField field Physical.coordinateZ)))

physicalFlatWilsonPlaquetteLevel : ProofLevel
physicalFlatWilsonPlaquetteLevel = machineChecked

physicalFlatWilsonPairSumLevel : ProofLevel
physicalFlatWilsonPairSumLevel = machineChecked

physicalFlatWilsonCurlIdentificationLevel : ProofLevel
physicalFlatWilsonCurlIdentificationLevel = machineChecked
