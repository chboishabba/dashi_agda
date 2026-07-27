module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (axisTransverse; insertAxis)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; physicalFibreSum; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalAdd)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
  using (axisAverage4RespectsPointwise)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using
    ( ScalarBondField4
    ; literalPeriodicDivergenceScalar
    ; literalNegativeForwardGradientScalar
    ; axis0
    ; axis1
    ; axis2
    ; axis3
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
  using (Lie3; lie3; x; y; z)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using
    ( Lie3SiteField
    ; componentScalarBondField
    ; literalPeriodicDivergence
    ; literalNegativeForwardGradient
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2LiteralWilsonOperatorRieszExact
  using (literalWilsonOperator)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using (fineProjection)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
  using (configuredGaugeFixedMatrix)
open import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
  using (applyMatrix; coordinates)
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
  using
    ( PhysicalSU2Coordinate4
    ; physicalFiniteRationalCoordinates
    ; tangentToCoordinateVector
    ; coordinateBasisTangent
    ; configuredGaugeFixedOperatorMatrix
    ; ConfiguredMatrixActionCertificate
    )

------------------------------------------------------------------------
-- Pointwise vector-space operations.
------------------------------------------------------------------------

addSiteField : SiteField side4 → SiteField side4 → SiteField side4
addSiteField left right site = left site + right site

scaleSiteField : ℚ → SiteField side4 → SiteField side4
scaleSiteField coefficient field site = coefficient * field site

addScalarBond : ScalarBondField4 → ScalarBondField4 → ScalarBondField4
addScalarBond left right axis site = left axis site + right axis site

scaleScalarBond : ℚ → ScalarBondField4 → ScalarBondField4
scaleScalarBond coefficient field axis site = coefficient * field axis site

addPhysical : PhysicalSU2Tangent4 → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
addPhysical left right component bond = left component bond + right component bond

scalePhysical : ℚ → PhysicalSU2Tangent4 → PhysicalSU2Tangent4
scalePhysical coefficient tangent component bond = coefficient * tangent component bond

zeroPhysical : PhysicalSU2Tangent4
zeroPhysical component bond = 0ℚ

addLie3 : Lie3 → Lie3 → Lie3
addLie3 (lie3 x₁ y₁ z₁) (lie3 x₂ y₂ z₂) =
  lie3 (x₁ + x₂) (y₁ + y₂) (z₁ + z₂)

scaleLie3 : ℚ → Lie3 → Lie3
scaleLie3 coefficient (lie3 x₁ y₁ z₁) =
  lie3 (coefficient * x₁) (coefficient * y₁) (coefficient * z₁)

addLie3Field : Lie3SiteField → Lie3SiteField → Lie3SiteField
addLie3Field left right site = addLie3 (left site) (right site)

scaleLie3Field : ℚ → Lie3SiteField → Lie3SiteField
scaleLie3Field coefficient field site = scaleLie3 coefficient (field site)

------------------------------------------------------------------------
-- Difference and average linearity.
------------------------------------------------------------------------

forwardDifferenceAdd : ∀ axis left right site →
  forwardDifference4 axis (addSiteField left right) site
  ≡ forwardDifference4 axis left site + forwardDifference4 axis right site
forwardDifferenceAdd axis left right site =
  ℚRing.solve-∀
    (left (shiftForward4 axis site)) (left site)
    (right (shiftForward4 axis site)) (right site)

forwardDifferenceScale : ∀ coefficient axis field site →
  forwardDifference4 axis (scaleSiteField coefficient field) site
  ≡ coefficient * forwardDifference4 axis field site
forwardDifferenceScale coefficient axis field site =
  ℚRing.solve-∀
    coefficient (field (shiftForward4 axis site)) (field site)

backwardDifferenceAdd : ∀ axis left right site →
  backwardDifference4 axis (addSiteField left right) site
  ≡ backwardDifference4 axis left site + backwardDifference4 axis right site
backwardDifferenceAdd axis left right site =
  ℚRing.solve-∀
    (left site) (left (shiftBackward4 axis site))
    (right site) (right (shiftBackward4 axis site))

backwardDifferenceScale : ∀ coefficient axis field site →
  backwardDifference4 axis (scaleSiteField coefficient field) site
  ≡ coefficient * backwardDifference4 axis field site
backwardDifferenceScale coefficient axis field site =
  ℚRing.solve-∀
    coefficient (field site) (field (shiftBackward4 axis site))

forwardDifferenceRespectsPointwise : ∀ axis {left right} →
  (∀ site → left site ≡ right site) →
  ∀ site → forwardDifference4 axis left site ≡ forwardDifference4 axis right site
forwardDifferenceRespectsPointwise axis pointwise site =
  cong₂ _-_
    (pointwise (shiftForward4 axis site))
    (pointwise site)

backwardDifferenceRespectsPointwise : ∀ axis {left right} →
  (∀ site → left site ≡ right site) →
  ∀ site → backwardDifference4 axis left site ≡ backwardDifference4 axis right site
backwardDifferenceRespectsPointwise axis pointwise site =
  cong₂ _-_
    (pointwise site)
    (pointwise (shiftBackward4 axis site))

physicalFibreSumAdd : ∀ left right axis transverse →
  physicalFibreSum (addSiteField left right) axis transverse
  ≡ physicalFibreSum left axis transverse
    + physicalFibreSum right axis transverse
physicalFibreSumAdd left right axis transverse =
  sumRationalAdd
    (allCyclicIndices side4)
    (λ coordinate → left (insertAxis axis coordinate transverse))
    (λ coordinate → right (insertAxis axis coordinate transverse))

physicalFibreSumScale : ∀ coefficient field axis transverse →
  physicalFibreSum (scaleSiteField coefficient field) axis transverse
  ≡ coefficient * physicalFibreSum field axis transverse
physicalFibreSumScale coefficient field axis transverse =
  DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
    coefficient
    (allCyclicIndices side4)
    (λ coordinate → field (insertAxis axis coordinate transverse))

axisAverageAdd : ∀ left right axis site →
  axisAverage4 (addSiteField left right) axis site
  ≡ addSiteField (axisAverage4 left axis) (axisAverage4 right axis) site
axisAverageAdd left right axis site =
  trans
    (cong (quarter *_) (physicalFibreSumAdd
      left right axis (axisTransverse axis site)))
    (ℚRing.solve-∀
      (physicalFibreSum left axis (axisTransverse axis site))
      (physicalFibreSum right axis (axisTransverse axis site)))

axisAverageScale : ∀ coefficient field axis site →
  axisAverage4 (scaleSiteField coefficient field) axis site
  ≡ scaleSiteField coefficient (axisAverage4 field axis) site
axisAverageScale coefficient field axis site =
  trans
    (cong (quarter *_) (physicalFibreSumScale
      coefficient field axis (axisTransverse axis site)))
    (ℚRing.solve-∀
      quarter coefficient
      (physicalFibreSum field axis (axisTransverse axis site)))

average0Add : ∀ left right site →
  average0 (addSiteField left right) site
  ≡ addSiteField (average0 left) (average0 right) site
average0Add left right = axisAverageAdd left right zeroᵢ

average01Add : ∀ left right site →
  average01 (addSiteField left right) site
  ≡ addSiteField (average01 left) (average01 right) site
average01Add left right site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ zeroᵢ)
      (average0Add left right) site)
    (axisAverageAdd (average0 left) (average0 right)
      (sucᵢ zeroᵢ) site)

average012Add : ∀ left right site →
  average012 (addSiteField left right) site
  ≡ addSiteField (average012 left) (average012 right) site
average012Add left right site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ zeroᵢ))
      (average01Add left right) site)
    (axisAverageAdd (average01 left) (average01 right)
      (sucᵢ (sucᵢ zeroᵢ)) site)

average0123Add : ∀ left right site →
  average0123 (addSiteField left right) site
  ≡ addSiteField (average0123 left) (average0123 right) site
average0123Add left right site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (average012Add left right) site)
    (axisAverageAdd (average012 left) (average012 right)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site)

average0Scale : ∀ coefficient field site →
  average0 (scaleSiteField coefficient field) site
  ≡ scaleSiteField coefficient (average0 field) site
average0Scale coefficient field = axisAverageScale coefficient field zeroᵢ

average01Scale : ∀ coefficient field site →
  average01 (scaleSiteField coefficient field) site
  ≡ scaleSiteField coefficient (average01 field) site
average01Scale coefficient field site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ zeroᵢ)
      (average0Scale coefficient field) site)
    (axisAverageScale coefficient (average0 field)
      (sucᵢ zeroᵢ) site)

average012Scale : ∀ coefficient field site →
  average012 (scaleSiteField coefficient field) site
  ≡ scaleSiteField coefficient (average012 field) site
average012Scale coefficient field site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ zeroᵢ))
      (average01Scale coefficient field) site)
    (axisAverageScale coefficient (average01 field)
      (sucᵢ (sucᵢ zeroᵢ)) site)

average0123Scale : ∀ coefficient field site →
  average0123 (scaleSiteField coefficient field) site
  ≡ scaleSiteField coefficient (average0123 field) site
average0123Scale coefficient field site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (average012Scale coefficient field) site)
    (axisAverageScale coefficient (average012 field)
      (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site)

average0123RespectsPointwise : ∀ {left right} →
  (∀ site → left site ≡ right site) →
  ∀ site → average0123 left site ≡ average0123 right site
average0123RespectsPointwise pointwise site =
  axisAverage4RespectsPointwise (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ zeroᵢ))
      (axisAverage4RespectsPointwise (sucᵢ zeroᵢ)
        (axisAverage4RespectsPointwise zeroᵢ pointwise))) site

------------------------------------------------------------------------
-- Wilson operator linearity.
------------------------------------------------------------------------

scalarPlaneCurlAdd : ∀ plane left right site →
  scalarPlaneCurl plane (addScalarBond left right) site
  ≡ scalarPlaneCurl plane left site + scalarPlaneCurl plane right site
scalarPlaneCurlAdd plane left right site
  rewrite forwardDifferenceAdd
    (positivePlaneFirst plane) (left (positivePlaneSecond plane))
      (right (positivePlaneSecond plane)) site
        | forwardDifferenceAdd
    (positivePlaneSecond plane) (left (positivePlaneFirst plane))
      (right (positivePlaneFirst plane)) site =
  ℚRing.solve-∀
    (forwardDifference4 (positivePlaneFirst plane)
      (left (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneFirst plane)
      (right (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (left (positivePlaneFirst plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (right (positivePlaneFirst plane)) site)

scalarPlaneCurlScale : ∀ coefficient plane field site →
  scalarPlaneCurl plane (scaleScalarBond coefficient field) site
  ≡ coefficient * scalarPlaneCurl plane field site
scalarPlaneCurlScale coefficient plane field site
  rewrite forwardDifferenceScale coefficient
    (positivePlaneFirst plane) (field (positivePlaneSecond plane)) site
        | forwardDifferenceScale coefficient
    (positivePlaneSecond plane) (field (positivePlaneFirst plane)) site =
  ℚRing.solve-∀
    coefficient
    (forwardDifference4 (positivePlaneFirst plane)
      (field (positivePlaneSecond plane)) site)
    (forwardDifference4 (positivePlaneSecond plane)
      (field (positivePlaneFirst plane)) site)

scalarPlaneCurlRespectsPointwise : ∀ plane {left right} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ site → scalarPlaneCurl plane left site ≡ scalarPlaneCurl plane right site
scalarPlaneCurlRespectsPointwise plane pointwise site =
  cong₂ _-_
    (forwardDifferenceRespectsPointwise (positivePlaneFirst plane)
      (pointwise (positivePlaneSecond plane)) site)
    (forwardDifferenceRespectsPointwise (positivePlaneSecond plane)
      (pointwise (positivePlaneFirst plane)) site)

backwardCurlAdd : ∀ axis plane left right site →
  backwardDifference4 axis
    (scalarPlaneCurl plane (addScalarBond left right)) site
  ≡ backwardDifference4 axis (scalarPlaneCurl plane left) site
    + backwardDifference4 axis (scalarPlaneCurl plane right) site
backwardCurlAdd axis plane left right site =
  trans
    (backwardDifferenceRespectsPointwise axis
      (scalarPlaneCurlAdd plane left right) site)
    (backwardDifferenceAdd axis
      (scalarPlaneCurl plane left) (scalarPlaneCurl plane right) site)

backwardCurlScale : ∀ coefficient axis plane field site →
  backwardDifference4 axis
    (scalarPlaneCurl plane (scaleScalarBond coefficient field)) site
  ≡ coefficient
    * backwardDifference4 axis (scalarPlaneCurl plane field) site
backwardCurlScale coefficient axis plane field site =
  trans
    (backwardDifferenceRespectsPointwise axis
      (scalarPlaneCurlScale coefficient plane field) site)
    (backwardDifferenceScale coefficient axis
      (scalarPlaneCurl plane field) site)

backwardCurlRespectsPointwise : ∀ axis plane {left right} →
  (∀ bondAxis site → left bondAxis site ≡ right bondAxis site) →
  ∀ site →
  backwardDifference4 axis (scalarPlaneCurl plane left) site
  ≡ backwardDifference4 axis (scalarPlaneCurl plane right) site
backwardCurlRespectsPointwise axis plane pointwise =
  backwardDifferenceRespectsPointwise axis
    (scalarPlaneCurlRespectsPointwise plane pointwise)

planeWilsonContributionAdd : ∀ plane left right axis site →
  planeWilsonContribution plane (addScalarBond left right) axis site
  ≡ planeWilsonContribution plane left axis site
    + planeWilsonContribution plane right axis site
planeWilsonContributionAdd plane01 left right zeroᵢ site =
  backwardCurlAdd axis1 plane01 left right site
planeWilsonContributionAdd plane01 left right (sucᵢ zeroᵢ) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane01 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 right) site))
planeWilsonContributionAdd plane01 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane01 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane02 left right zeroᵢ site =
  backwardCurlAdd axis2 plane02 left right site
planeWilsonContributionAdd plane02 left right (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane02 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane02 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 right) site))
planeWilsonContributionAdd plane02 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane03 left right zeroᵢ site =
  backwardCurlAdd axis3 plane03 left right site
planeWilsonContributionAdd plane03 left right (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane03 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane03 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane03 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 right) site))
planeWilsonContributionAdd plane12 left right zeroᵢ site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane12 left right (sucᵢ zeroᵢ) site =
  backwardCurlAdd axis2 plane12 left right site
planeWilsonContributionAdd plane12 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlAdd axis1 plane12 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 left) site)
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 right) site))
planeWilsonContributionAdd plane12 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane13 left right zeroᵢ site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane13 left right (sucᵢ zeroᵢ) site =
  backwardCurlAdd axis3 plane13 left right site
planeWilsonContributionAdd plane13 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane13 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis1 plane13 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 left) site)
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 right) site))
planeWilsonContributionAdd plane23 left right zeroᵢ site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane23 left right (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀
planeWilsonContributionAdd plane23 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  backwardCurlAdd axis3 plane23 left right site
planeWilsonContributionAdd plane23 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis2 plane23 left right site))
    (ℚRing.solve-∀
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 left) site)
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 right) site))

planeWilsonContributionScale : ∀ coefficient plane field axis site →
  planeWilsonContribution plane (scaleScalarBond coefficient field) axis site
  ≡ coefficient * planeWilsonContribution plane field axis site
planeWilsonContributionScale coefficient plane01 field zeroᵢ site =
  backwardCurlScale coefficient axis1 plane01 field site
planeWilsonContributionScale coefficient plane01 field (sucᵢ zeroᵢ) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane01 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 field) site))
planeWilsonContributionScale coefficient plane01 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane01 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane02 field zeroᵢ site =
  backwardCurlScale coefficient axis2 plane02 field site
planeWilsonContributionScale coefficient plane02 field (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane02 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane02 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 field) site))
planeWilsonContributionScale coefficient plane02 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane03 field zeroᵢ site =
  backwardCurlScale coefficient axis3 plane03 field site
planeWilsonContributionScale coefficient plane03 field (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane03 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane03 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane03 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 field) site))
planeWilsonContributionScale coefficient plane12 field zeroᵢ site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane12 field (sucᵢ zeroᵢ) site =
  backwardCurlScale coefficient axis2 plane12 field site
planeWilsonContributionScale coefficient plane12 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis1 plane12 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 field) site))
planeWilsonContributionScale coefficient plane12 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane13 field zeroᵢ site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane13 field (sucᵢ zeroᵢ) site =
  backwardCurlScale coefficient axis3 plane13 field site
planeWilsonContributionScale coefficient plane13 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane13 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis1 plane13 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 field) site))
planeWilsonContributionScale coefficient plane23 field zeroᵢ site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane23 field (sucᵢ zeroᵢ) site =
  ℚRing.solve-∀ coefficient
planeWilsonContributionScale coefficient plane23 field
    (sucᵢ (sucᵢ zeroᵢ)) site =
  backwardCurlScale coefficient axis3 plane23 field site
planeWilsonContributionScale coefficient plane23 field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis2 plane23 field site))
    (ℚRing.solve-∀ coefficient
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 field) site))

planeWilsonContributionRespectsPointwise :
  ∀ plane {left right} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ axis site →
  planeWilsonContribution plane left axis site
  ≡ planeWilsonContribution plane right axis site
planeWilsonContributionRespectsPointwise plane01 pointwise zeroᵢ =
  backwardCurlRespectsPointwise axis1 plane01 pointwise
planeWilsonContributionRespectsPointwise plane01 pointwise (sucᵢ zeroᵢ) site =
  cong -_ (backwardCurlRespectsPointwise axis0 plane01 pointwise site)
planeWilsonContributionRespectsPointwise plane01 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) site = refl
planeWilsonContributionRespectsPointwise plane01 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site = refl
planeWilsonContributionRespectsPointwise plane02 pointwise zeroᵢ =
  backwardCurlRespectsPointwise axis2 plane02 pointwise
planeWilsonContributionRespectsPointwise plane02 pointwise
    (sucᵢ zeroᵢ) site = refl
planeWilsonContributionRespectsPointwise plane02 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) site =
  cong -_ (backwardCurlRespectsPointwise axis0 plane02 pointwise site)
planeWilsonContributionRespectsPointwise plane02 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site = refl
planeWilsonContributionRespectsPointwise plane03 pointwise zeroᵢ =
  backwardCurlRespectsPointwise axis3 plane03 pointwise
planeWilsonContributionRespectsPointwise plane03 pointwise
    (sucᵢ zeroᵢ) site = refl
planeWilsonContributionRespectsPointwise plane03 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) site = refl
planeWilsonContributionRespectsPointwise plane03 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  cong -_ (backwardCurlRespectsPointwise axis0 plane03 pointwise site)
planeWilsonContributionRespectsPointwise plane12 pointwise zeroᵢ site = refl
planeWilsonContributionRespectsPointwise plane12 pointwise
    (sucᵢ zeroᵢ) =
  backwardCurlRespectsPointwise axis2 plane12 pointwise
planeWilsonContributionRespectsPointwise plane12 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) site =
  cong -_ (backwardCurlRespectsPointwise axis1 plane12 pointwise site)
planeWilsonContributionRespectsPointwise plane12 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site = refl
planeWilsonContributionRespectsPointwise plane13 pointwise zeroᵢ site = refl
planeWilsonContributionRespectsPointwise plane13 pointwise
    (sucᵢ zeroᵢ) =
  backwardCurlRespectsPointwise axis3 plane13 pointwise
planeWilsonContributionRespectsPointwise plane13 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) site = refl
planeWilsonContributionRespectsPointwise plane13 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  cong -_ (backwardCurlRespectsPointwise axis1 plane13 pointwise site)
planeWilsonContributionRespectsPointwise plane23 pointwise zeroᵢ site = refl
planeWilsonContributionRespectsPointwise plane23 pointwise
    (sucᵢ zeroᵢ) site = refl
planeWilsonContributionRespectsPointwise plane23 pointwise
    (sucᵢ (sucᵢ zeroᵢ)) =
  backwardCurlRespectsPointwise axis3 plane23 pointwise
planeWilsonContributionRespectsPointwise plane23 pointwise
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  cong -_ (backwardCurlRespectsPointwise axis2 plane23 pointwise site)

scalarWilsonOperatorAdd : ∀ left right axis site →
  scalarWilsonOperator (addScalarBond left right) axis site
  ≡ scalarWilsonOperator left axis site + scalarWilsonOperator right axis site
scalarWilsonOperatorAdd left right axis site =
  trans
    (sumRationalCong positivePlaquettePlanes4 _ _
      (λ plane → planeWilsonContributionAdd plane left right axis site))
    (sumRationalAdd positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane left axis site)
      (λ plane → planeWilsonContribution plane right axis site))

scalarWilsonOperatorScale : ∀ coefficient field axis site →
  scalarWilsonOperator (scaleScalarBond coefficient field) axis site
  ≡ coefficient * scalarWilsonOperator field axis site
scalarWilsonOperatorScale coefficient field axis site =
  trans
    (sumRationalCong positivePlaquettePlanes4 _ _
      (λ plane → planeWilsonContributionScale
        coefficient plane field axis site))
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
      coefficient positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane field axis site))

scalarWilsonOperatorRespectsPointwise :
  ∀ {left right} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ axis site →
  scalarWilsonOperator left axis site ≡ scalarWilsonOperator right axis site
scalarWilsonOperatorRespectsPointwise pointwise axis site =
  sumRationalCong positivePlaquettePlanes4 _ _
    (λ plane →
      planeWilsonContributionRespectsPointwise plane pointwise axis site)

literalWilsonOperatorAdd : ∀ left right component bond →
  literalWilsonOperator (addPhysical left right) component bond
  ≡ literalWilsonOperator left component bond
    + literalWilsonOperator right component bond
literalWilsonOperatorAdd left right component (pair site axis) =
  scalarWilsonOperatorAdd
    (componentScalarBondField left component)
    (componentScalarBondField right component)
    axis site

literalWilsonOperatorScale : ∀ coefficient tangent component bond →
  literalWilsonOperator (scalePhysical coefficient tangent) component bond
  ≡ coefficient * literalWilsonOperator tangent component bond
literalWilsonOperatorScale coefficient tangent component (pair site axis) =
  scalarWilsonOperatorScale coefficient
    (componentScalarBondField tangent component) axis site

literalWilsonOperatorRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ component bond →
  literalWilsonOperator left component bond
  ≡ literalWilsonOperator right component bond
literalWilsonOperatorRespectsPointwise pointwise component (pair site axis) =
  scalarWilsonOperatorRespectsPointwise
    (λ bondAxis currentSite →
      pointwise component (pair currentSite bondAxis))
    axis site

------------------------------------------------------------------------
-- Divergence, gauge penalty, and coarse projection linearity.
------------------------------------------------------------------------

literalPeriodicDivergenceScalarAdd : ∀ left right site →
  literalPeriodicDivergenceScalar (addScalarBond left right) site
  ≡ literalPeriodicDivergenceScalar left site
    + literalPeriodicDivergenceScalar right site
literalPeriodicDivergenceScalarAdd left right site =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → backwardDifferenceAdd axis
        (left axis) (right axis) site))
    (sumRationalAdd (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (left axis) site)
      (λ axis → backwardDifference4 axis (right axis) site))

literalPeriodicDivergenceScalarScale : ∀ coefficient field site →
  literalPeriodicDivergenceScalar (scaleScalarBond coefficient field) site
  ≡ coefficient * literalPeriodicDivergenceScalar field site
literalPeriodicDivergenceScalarScale coefficient field site =
  trans
    (sumRationalCong (allCyclicIndices four) _ _
      (λ axis → backwardDifferenceScale coefficient axis (field axis) site))
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
      coefficient (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (field axis) site))

literalPeriodicDivergenceScalarRespectsPointwise :
  ∀ {left right} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ site →
  literalPeriodicDivergenceScalar left site
  ≡ literalPeriodicDivergenceScalar right site
literalPeriodicDivergenceScalarRespectsPointwise pointwise site =
  sumRationalCong (allCyclicIndices four) _ _
    (λ axis → backwardDifferenceRespectsPointwise axis
      (pointwise axis) site)

literalPeriodicDivergenceAdd : ∀ left right site →
  literalPeriodicDivergence (addPhysical left right) site
  ≡ addLie3 (literalPeriodicDivergence left site)
      (literalPeriodicDivergence right site)
literalPeriodicDivergenceAdd left right site
  rewrite literalPeriodicDivergenceScalarAdd
    (componentScalarBondField left component1)
    (componentScalarBondField right component1) site
      | literalPeriodicDivergenceScalarAdd
    (componentScalarBondField left component2)
    (componentScalarBondField right component2) site
      | literalPeriodicDivergenceScalarAdd
    (componentScalarBondField left component3)
    (componentScalarBondField right component3) site = refl

literalPeriodicDivergenceScale : ∀ coefficient tangent site →
  literalPeriodicDivergence (scalePhysical coefficient tangent) site
  ≡ scaleLie3 coefficient (literalPeriodicDivergence tangent site)
literalPeriodicDivergenceScale coefficient tangent site
  rewrite literalPeriodicDivergenceScalarScale coefficient
    (componentScalarBondField tangent component1) site
      | literalPeriodicDivergenceScalarScale coefficient
    (componentScalarBondField tangent component2) site
      | literalPeriodicDivergenceScalarScale coefficient
    (componentScalarBondField tangent component3) site = refl

cong3 :
  ∀ {A B C D : Set} {f : A → B → C → D}
    {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ →
  f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong3 refl refl refl = refl

literalPeriodicDivergenceRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ site →
  literalPeriodicDivergence left site ≡ literalPeriodicDivergence right site
literalPeriodicDivergenceRespectsPointwise pointwise site =
  cong3
    (literalPeriodicDivergenceScalarRespectsPointwise
      (λ axis currentSite →
        pointwise component1 (pair currentSite axis)) site)
    (literalPeriodicDivergenceScalarRespectsPointwise
      (λ axis currentSite →
        pointwise component2 (pair currentSite axis)) site)
    (literalPeriodicDivergenceScalarRespectsPointwise
      (λ axis currentSite →
        pointwise component3 (pair currentSite axis)) site)

lie3ComponentAdd : ∀ component left right →
  DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
    component (addLie3 left right)
  ≡ DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
      component left
    + DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
      component right
lie3ComponentAdd component1 (lie3 x₁ y₁ z₁) (lie3 x₂ y₂ z₂) = refl
lie3ComponentAdd component2 (lie3 x₁ y₁ z₁) (lie3 x₂ y₂ z₂) = refl
lie3ComponentAdd component3 (lie3 x₁ y₁ z₁) (lie3 x₂ y₂ z₂) = refl

lie3ComponentScale : ∀ coefficient component value →
  DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
    component (scaleLie3 coefficient value)
  ≡ coefficient
    * DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
      component value
lie3ComponentScale coefficient component1 (lie3 x₁ y₁ z₁) = refl
lie3ComponentScale coefficient component2 (lie3 x₁ y₁ z₁) = refl
lie3ComponentScale coefficient component3 (lie3 x₁ y₁ z₁) = refl

literalNegativeForwardGradientAdd : ∀ left right component bond →
  literalNegativeForwardGradient (addLie3Field left right) component bond
  ≡ literalNegativeForwardGradient left component bond
    + literalNegativeForwardGradient right component bond
literalNegativeForwardGradientAdd left right component (pair site axis) =
  trans
    (cong -_
      (trans
        (forwardDifferenceRespectsPointwise axis
          (λ current → lie3ComponentAdd component (left current) (right current))
          site)
        (forwardDifferenceAdd axis
          (λ current →
            DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
              component (left current))
          (λ current →
            DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
              component (right current))
          site)))
    (ℚRing.solve-∀
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (left current)) site)
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (right current)) site))

literalNegativeForwardGradientScale : ∀ coefficient field component bond →
  literalNegativeForwardGradient (scaleLie3Field coefficient field) component bond
  ≡ coefficient * literalNegativeForwardGradient field component bond
literalNegativeForwardGradientScale coefficient field component (pair site axis) =
  trans
    (cong -_
      (trans
        (forwardDifferenceRespectsPointwise axis
          (λ current → lie3ComponentScale coefficient component (field current))
          site)
        (forwardDifferenceScale coefficient axis
          (λ current →
            DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
              component (field current))
          site)))
    (ℚRing.solve-∀ coefficient
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (field current)) site))

literalNegativeForwardGradientRespectsPointwise :
  ∀ {left right} →
  (∀ site → left site ≡ right site) →
  ∀ component bond →
  literalNegativeForwardGradient left component bond
  ≡ literalNegativeForwardGradient right component bond
literalNegativeForwardGradientRespectsPointwise pointwise component
    (pair site axis) =
  cong -_
    (forwardDifferenceRespectsPointwise axis
      (λ current → cong
        (DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
          component)
        (pointwise current))
      site)

literalGaugePenalty : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
literalGaugePenalty tangent =
  literalNegativeForwardGradient (literalPeriodicDivergence tangent)

literalGaugePenaltyAdd : ∀ left right component bond →
  literalGaugePenalty (addPhysical left right) component bond
  ≡ literalGaugePenalty left component bond
    + literalGaugePenalty right component bond
literalGaugePenaltyAdd left right component bond =
  trans
    (literalNegativeForwardGradientRespectsPointwise
      (literalPeriodicDivergenceAdd left right) component bond)
    (literalNegativeForwardGradientAdd
      (literalPeriodicDivergence left)
      (literalPeriodicDivergence right)
      component bond)

literalGaugePenaltyScale : ∀ coefficient tangent component bond →
  literalGaugePenalty (scalePhysical coefficient tangent) component bond
  ≡ coefficient * literalGaugePenalty tangent component bond
literalGaugePenaltyScale coefficient tangent component bond =
  trans
    (literalNegativeForwardGradientRespectsPointwise
      (literalPeriodicDivergenceScale coefficient tangent) component bond)
    (literalNegativeForwardGradientScale coefficient
      (literalPeriodicDivergence tangent) component bond)

literalGaugePenaltyRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ component bond →
  literalGaugePenalty left component bond
  ≡ literalGaugePenalty right component bond
literalGaugePenaltyRespectsPointwise pointwise =
  literalNegativeForwardGradientRespectsPointwise
    (literalPeriodicDivergenceRespectsPointwise pointwise)

fineProjectionAdd : ∀ left right component bond →
  fineProjection (addPhysical left right) component bond
  ≡ fineProjection left component bond + fineProjection right component bond
fineProjectionAdd left right component (pair site axis) =
  average0123Add
    (componentScalarBondField left component axis)
    (componentScalarBondField right component axis)
    site

fineProjectionScale : ∀ coefficient tangent component bond →
  fineProjection (scalePhysical coefficient tangent) component bond
  ≡ coefficient * fineProjection tangent component bond
fineProjectionScale coefficient tangent component (pair site axis) =
  average0123Scale coefficient
    (componentScalarBondField tangent component axis)
    site

fineProjectionRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ component bond →
  fineProjection left component bond ≡ fineProjection right component bond
fineProjectionRespectsPointwise pointwise component (pair site axis) =
  average0123RespectsPointwise
    (λ current → pointwise component (pair current axis)) site

------------------------------------------------------------------------
-- Complete configured operator linearity.
------------------------------------------------------------------------

configuredGaugeFixedMatrixPointwise : ∀ tangent component bond →
  configuredGaugeFixedMatrix tangent component bond
  ≡ literalWilsonOperator tangent component bond
    + (literalGaugePenalty tangent component bond
      + fineProjection tangent component bond)
configuredGaugeFixedMatrixPointwise tangent component bond = refl

configuredGaugeFixedMatrixAdd : ∀ left right component bond →
  configuredGaugeFixedMatrix (addPhysical left right) component bond
  ≡ configuredGaugeFixedMatrix left component bond
    + configuredGaugeFixedMatrix right component bond
configuredGaugeFixedMatrixAdd left right component bond =
  trans
    (configuredGaugeFixedMatrixPointwise
      (addPhysical left right) component bond)
    (trans
      (cong₂ _+_
        (literalWilsonOperatorAdd left right component bond)
        (cong₂ _+_
          (literalGaugePenaltyAdd left right component bond)
          (fineProjectionAdd left right component bond)))
      (trans
        (ℚRing.solve-∀
          (literalWilsonOperator left component bond)
          (literalWilsonOperator right component bond)
          (literalGaugePenalty left component bond)
          (literalGaugePenalty right component bond)
          (fineProjection left component bond)
          (fineProjection right component bond))
        (cong₂ _+_
          (sym (configuredGaugeFixedMatrixPointwise left component bond))
          (sym (configuredGaugeFixedMatrixPointwise right component bond)))))

configuredGaugeFixedMatrixScale : ∀ coefficient tangent component bond →
  configuredGaugeFixedMatrix (scalePhysical coefficient tangent) component bond
  ≡ coefficient * configuredGaugeFixedMatrix tangent component bond
configuredGaugeFixedMatrixScale coefficient tangent component bond =
  trans
    (configuredGaugeFixedMatrixPointwise
      (scalePhysical coefficient tangent) component bond)
    (trans
      (cong₂ _+_
        (literalWilsonOperatorScale coefficient tangent component bond)
        (cong₂ _+_
          (literalGaugePenaltyScale coefficient tangent component bond)
          (fineProjectionScale coefficient tangent component bond)))
      (trans
        (ℚRing.solve-∀ coefficient
          (literalWilsonOperator tangent component bond)
          (literalGaugePenalty tangent component bond)
          (fineProjection tangent component bond))
        (cong (coefficient *_)
          (sym (configuredGaugeFixedMatrixPointwise tangent component bond)))))

configuredGaugeFixedMatrixRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ component bond →
  configuredGaugeFixedMatrix left component bond
  ≡ configuredGaugeFixedMatrix right component bond
configuredGaugeFixedMatrixRespectsPointwise pointwise component bond =
  trans
    (configuredGaugeFixedMatrixPointwise left component bond)
    (trans
      (cong₂ _+_
        (literalWilsonOperatorRespectsPointwise pointwise component bond)
        (cong₂ _+_
          (literalGaugePenaltyRespectsPointwise pointwise component bond)
          (fineProjectionRespectsPointwise pointwise component bond)))
      (sym (configuredGaugeFixedMatrixPointwise right component bond)))

configuredGaugeFixedMatrixZero : ∀ component bond →
  configuredGaugeFixedMatrix zeroPhysical component bond ≡ 0ℚ
configuredGaugeFixedMatrixZero component bond =
  trans
    (configuredGaugeFixedMatrixRespectsPointwise
      (λ current currentBond →
        ℚRing.solve-∀ (zeroPhysical current currentBond))
      component bond)
    (trans
      (configuredGaugeFixedMatrixScale 0ℚ zeroPhysical component bond)
      (ℚRing.solve-∀
        (configuredGaugeFixedMatrix zeroPhysical component bond)))

------------------------------------------------------------------------
-- Finite basis expansion and literal matrix action.
------------------------------------------------------------------------

sumPhysical :
  ∀ {Index : Set} → List Index → (Index → PhysicalSU2Tangent4) →
  PhysicalSU2Tangent4
sumPhysical [] term = zeroPhysical
sumPhysical (value ∷ values) term =
  addPhysical (term value) (sumPhysical values term)

sumPhysicalPointwise :
  ∀ {Index : Set} (values : List Index)
    (term : Index → PhysicalSU2Tangent4) component bond →
  sumPhysical values term component bond
  ≡ sumRational values (λ value → term value component bond)
sumPhysicalPointwise [] term component bond = refl
sumPhysicalPointwise (value ∷ values) term component bond
  rewrite sumPhysicalPointwise values term component bond = refl

configuredGaugeFixedMatrixSum :
  ∀ {Index : Set} (values : List Index)
    (term : Index → PhysicalSU2Tangent4) component bond →
  configuredGaugeFixedMatrix (sumPhysical values term) component bond
  ≡ sumRational values
      (λ value → configuredGaugeFixedMatrix (term value) component bond)
configuredGaugeFixedMatrixSum [] term component bond =
  configuredGaugeFixedMatrixZero component bond
configuredGaugeFixedMatrixSum (value ∷ values) term component bond =
  trans
    (configuredGaugeFixedMatrixAdd
      (term value) (sumPhysical values term) component bond)
    (cong₂ _+_ refl
      (configuredGaugeFixedMatrixSum values term component bond))

basisExpansionPointwise : ∀ tangent component bond →
  sumPhysical
    (coordinates physicalFiniteRationalCoordinates)
    (λ column →
      scalePhysical
        (tangentToCoordinateVector tangent column)
        (coordinateBasisTangent column))
    component bond
  ≡ tangent component bond
basisExpansionPointwise tangent component bond =
  trans
    (sumPhysicalPointwise
      (coordinates physicalFiniteRationalCoordinates)
      (λ column →
        scalePhysical
          (tangentToCoordinateVector tangent column)
          (coordinateBasisTangent column))
      component bond)
    (trans
      (sumRationalCong
        (coordinates physicalFiniteRationalCoordinates)
        (λ column →
          tangentToCoordinateVector tangent column
          * coordinateBasisTangent column component bond)
        (λ column →
          DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.delta
            physicalFiniteRationalCoordinates
            (pair component bond) column
          * tangentToCoordinateVector tangent column)
        (λ column → ℚRing.solve-∀
          (tangentToCoordinateVector tangent column)
          (coordinateBasisTangent column component bond)))
      (DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.deltaActsAsIdentity
        physicalFiniteRationalCoordinates
        (tangentToCoordinateVector tangent)
        (pair component bond)))

configuredMatrixActsExactly : ∀ tangent row →
  applyMatrix
    physicalFiniteRationalCoordinates
    configuredGaugeFixedOperatorMatrix
    (tangentToCoordinateVector tangent)
    row
  ≡ tangentToCoordinateVector (configuredGaugeFixedMatrix tangent) row
configuredMatrixActsExactly tangent (pair component bond) =
  trans
    (sumRationalCong
      (coordinates physicalFiniteRationalCoordinates)
      (λ column →
        configuredGaugeFixedMatrix
          (coordinateBasisTangent column) component bond
        * tangentToCoordinateVector tangent column)
      (λ column →
        tangentToCoordinateVector tangent column
        * configuredGaugeFixedMatrix
          (coordinateBasisTangent column) component bond)
      (λ column → ℚRing.solve-∀
        (configuredGaugeFixedMatrix
          (coordinateBasisTangent column) component bond)
        (tangentToCoordinateVector tangent column)))
    (trans
      (sumRationalCong
        (coordinates physicalFiniteRationalCoordinates)
        (λ column →
          tangentToCoordinateVector tangent column
          * configuredGaugeFixedMatrix
              (coordinateBasisTangent column) component bond)
        (λ column →
          configuredGaugeFixedMatrix
            (scalePhysical
              (tangentToCoordinateVector tangent column)
              (coordinateBasisTangent column))
            component bond)
        (λ column →
          sym (configuredGaugeFixedMatrixScale
            (tangentToCoordinateVector tangent column)
            (coordinateBasisTangent column)
            component bond)))
      (trans
        (sym
          (configuredGaugeFixedMatrixSum
            (coordinates physicalFiniteRationalCoordinates)
            (λ column →
              scalePhysical
                (tangentToCoordinateVector tangent column)
                (coordinateBasisTangent column))
            component bond))
        (configuredGaugeFixedMatrixRespectsPointwise
          (basisExpansionPointwise tangent)
          component bond)))

literalConfiguredMatrixActionCertificate :
  ConfiguredMatrixActionCertificate
literalConfiguredMatrixActionCertificate = record
  { DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact.configuredMatrixActsExactly =
      configuredMatrixActsExactly
  }

configuredGaugeFixedOperatorAdditivityLevel : ProofLevel
configuredGaugeFixedOperatorAdditivityLevel = machineChecked

configuredGaugeFixedOperatorHomogeneityLevel : ProofLevel
configuredGaugeFixedOperatorHomogeneityLevel = machineChecked

configuredGaugeFixedOperatorPointwiseCongruenceLevel : ProofLevel
configuredGaugeFixedOperatorPointwiseCongruenceLevel = machineChecked

configuredMatrixActionLinearityLevel : ProofLevel
configuredMatrixActionLinearityLevel = machineChecked
