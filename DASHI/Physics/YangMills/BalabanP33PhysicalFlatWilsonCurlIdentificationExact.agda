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
asPeriodicPhysicalField fieldValue coordinate axis site =
  fieldValue coordinate (pair site axis)

insertionAt :
  Physical.PhysicalSU2BondField4 →
  Axis4 → Hodge4.Site4 → Wilson.RationalVector3
insertionAt fieldValue axis site =
  Wilson.vec3
    (fieldValue Physical.coordinateX (pair site axis))
    (fieldValue Physical.coordinateY (pair site axis))
    (fieldValue Physical.coordinateZ (pair site axis))

flatPlaquetteSecondVariation :
  Physical.PhysicalSU2BondField4 →
  Axis4 → Axis4 → Hodge4.Site4 → ℚ
flatPlaquetteSecondVariation fieldValue left right site =
  Wilson.flatOrientedPlaquetteSecondVariation
    (insertionAt fieldValue left site)
    (insertionAt fieldValue right (Hodge4.shiftForward left site))
    (insertionAt fieldValue left (Hodge4.shiftForward right site))
    (insertionAt fieldValue right site)

plaquetteCurlCoordinate :
  Physical.PhysicalSU2BondField4 →
  Physical.LieCoordinate3 → Axis4 → Axis4 → Hodge4.Site4 → ℚ
plaquetteCurlCoordinate fieldValue coordinate left right site =
  Hodge4.curlComponent left right
    (asPeriodicPhysicalField fieldValue coordinate) site

flatPlaquetteSecondVariationIsPhysicalCurlSquare :
  ∀ fieldValue left right site →
  flatPlaquetteSecondVariation fieldValue left right site
  ≡
    plaquetteCurlCoordinate fieldValue Physical.coordinateX left right site
      * plaquetteCurlCoordinate fieldValue Physical.coordinateX left right site
    + plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site
      * plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site
    + plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site
      * plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site
flatPlaquetteSecondVariationIsPhysicalCurlSquare
    fieldValue left right site =
  trans
    (Wilson.flatPlaquetteWilsonIsCurlSquare
      (insertionAt fieldValue left site)
      (insertionAt fieldValue right (Hodge4.shiftForward left site))
      (insertionAt fieldValue left (Hodge4.shiftForward right site))
      (insertionAt fieldValue right site))
    (ℚRing.solve-∀
      (fieldValue Physical.coordinateX (pair site left))
      (fieldValue Physical.coordinateY (pair site left))
      (fieldValue Physical.coordinateZ (pair site left))
      (fieldValue Physical.coordinateX
        (pair (Hodge4.shiftForward left site) right))
      (fieldValue Physical.coordinateY
        (pair (Hodge4.shiftForward left site) right))
      (fieldValue Physical.coordinateZ
        (pair (Hodge4.shiftForward left site) right))
      (fieldValue Physical.coordinateX
        (pair (Hodge4.shiftForward right site) left))
      (fieldValue Physical.coordinateY
        (pair (Hodge4.shiftForward right site) left))
      (fieldValue Physical.coordinateZ
        (pair (Hodge4.shiftForward right site) left))
      (fieldValue Physical.coordinateX (pair site right))
      (fieldValue Physical.coordinateY (pair site right))
      (fieldValue Physical.coordinateZ (pair site right)))

------------------------------------------------------------------------
-- Six-pair physical sum.
------------------------------------------------------------------------

flatPlaquettePairEnergy :
  Physical.PhysicalSU2BondField4 → Axis4 → Axis4 → ℚ
flatPlaquettePairEnergy fieldValue left right =
  Hodge4.sumSites
    (flatPlaquetteSecondVariation fieldValue left right)

physicalPairCurlEnergy :
  Physical.PhysicalSU2BondField4 → Axis4 → Axis4 → ℚ
physicalPairCurlEnergy fieldValue left right =
  Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField fieldValue Physical.coordinateX))
  + Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField fieldValue Physical.coordinateY))
  + Hodge4.fieldNormSq
    (Hodge4.curlComponent left right
      (asPeriodicPhysicalField fieldValue Physical.coordinateZ))

flatPlaquettePairEnergyIsPhysicalCurl : ∀ fieldValue left right →
  flatPlaquettePairEnergy fieldValue left right
  ≡ physicalPairCurlEnergy fieldValue left right
flatPlaquettePairEnergyIsPhysicalCurl fieldValue left right =
  trans
    (Hodge4.sumSitesCong _ _
      (flatPlaquetteSecondVariationIsPhysicalCurlSquare
        fieldValue left right))
    (trans
      (Hodge4.sumSitesAdd
        (λ site →
          plaquetteCurlCoordinate fieldValue Physical.coordinateX left right site
          * plaquetteCurlCoordinate fieldValue Physical.coordinateX left right site)
        (λ site →
          plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site
          * plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site
          + plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site
          * plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site))
      (trans
        (cong
          (Hodge4.fieldNormSq
            (Hodge4.curlComponent left right
              (asPeriodicPhysicalField fieldValue Physical.coordinateX)) +_)
          (Hodge4.sumSitesAdd
            (λ site →
              plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site
              * plaquetteCurlCoordinate fieldValue Physical.coordinateY left right site)
            (λ site →
              plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site
              * plaquetteCurlCoordinate fieldValue Physical.coordinateZ left right site)))
        refl))

flatWilsonEnergy : Physical.PhysicalSU2BondField4 → ℚ
flatWilsonEnergy fieldValue =
  flatPlaquettePairEnergy fieldValue Hodge4.axis0 Hodge4.axis1
  + flatPlaquettePairEnergy fieldValue Hodge4.axis0 Hodge4.axis2
  + flatPlaquettePairEnergy fieldValue Hodge4.axis0 Hodge4.axis3
  + flatPlaquettePairEnergy fieldValue Hodge4.axis1 Hodge4.axis2
  + flatPlaquettePairEnergy fieldValue Hodge4.axis1 Hodge4.axis3
  + flatPlaquettePairEnergy fieldValue Hodge4.axis2 Hodge4.axis3

flatWilsonEnergyIsPhysicalPeriodicCurl : ∀ fieldValue →
  flatWilsonEnergy fieldValue
  ≡ Hodge4.physicalPeriodicCurlEnergy (asPeriodicPhysicalField fieldValue)
flatWilsonEnergyIsPhysicalPeriodicCurl fieldValue
  rewrite flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis0 Hodge4.axis1
  | flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis0 Hodge4.axis2
  | flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis0 Hodge4.axis3
  | flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis1 Hodge4.axis2
  | flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis1 Hodge4.axis3
  | flatPlaquettePairEnergyIsPhysicalCurl
    fieldValue Hodge4.axis2 Hodge4.axis3 =
  ℚRing.solve-∀
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateX)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateY)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis1
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis0 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis2
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis1 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))
    (Hodge4.fieldNormSq
      (Hodge4.curlComponent Hodge4.axis2 Hodge4.axis3
        (asPeriodicPhysicalField fieldValue Physical.coordinateZ)))

physicalFlatWilsonPlaquetteLevel : ProofLevel
physicalFlatWilsonPlaquetteLevel = machineChecked

physicalFlatWilsonPairSumLevel : ProofLevel
physicalFlatWilsonPairSumLevel = machineChecked

physicalFlatWilsonCurlIdentificationLevel : ProofLevel
physicalFlatWilsonCurlIdentificationLevel = machineChecked
