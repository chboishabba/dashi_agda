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
  (SiteField; physicalFibreSum; sumRational; sumRationalCong; sumRationalScale)
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
  hiding (mulZeroRightRaw)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2WilsonPlaquetteSecondJetExact
  using (Lie3; lie3; x; y; z)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using
    ( Lie3SiteField
    ; lie3Component
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
  using (applyMatrix; coordinates; delta; deltaActsAsIdentity)
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
scaleSiteField coefficient fld site = coefficient * fld site

addScalarBond : ScalarBondField4 → ScalarBondField4 → ScalarBondField4
addScalarBond left right axis site = left axis site + right axis site

scaleScalarBond : ℚ → ScalarBondField4 → ScalarBondField4
scaleScalarBond coefficient fld axis site = coefficient * fld axis site

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
scaleLie3Field coefficient fld site = scaleLie3 coefficient (fld site)

------------------------------------------------------------------------
-- Difference and average linearity.
------------------------------------------------------------------------

diffAddRaw : ∀ a1 a2 b1 b2 → (a1 + b1) - (a2 + b2) ≡ (a1 - a2) + (b1 - b2)
diffAddRaw = ℚRing.solve-∀

diffScaleRaw : ∀ c a b → c * a - c * b ≡ c * (a - b)
diffScaleRaw = ℚRing.solve-∀

forwardDifferenceAdd : ∀ axis left right site →
  forwardDifference4 axis (addSiteField left right) site
  ≡ forwardDifference4 axis left site + forwardDifference4 axis right site
forwardDifferenceAdd axis left right site =
  diffAddRaw
    (left (shiftForward4 axis site))
    (left site)
    (right (shiftForward4 axis site))
    (right site)

forwardDifferenceScale : ∀ coefficient axis fld site →
  forwardDifference4 axis (scaleSiteField coefficient fld) site
  ≡ coefficient * forwardDifference4 axis fld site
forwardDifferenceScale coefficient axis fld site =
  diffScaleRaw
    coefficient
    (fld (shiftForward4 axis site))
    (fld site)

backwardDifferenceAdd : ∀ axis left right site →
  backwardDifference4 axis (addSiteField left right) site
  ≡ backwardDifference4 axis left site + backwardDifference4 axis right site
backwardDifferenceAdd axis left right site =
  diffAddRaw
    (left site)
    (left (shiftBackward4 axis site))
    (right site)
    (right (shiftBackward4 axis site))

backwardDifferenceScale : ∀ coefficient axis fld site →
  backwardDifference4 axis (scaleSiteField coefficient fld) site
  ≡ coefficient * backwardDifference4 axis fld site
backwardDifferenceScale coefficient axis fld site =
  diffScaleRaw
    coefficient
    (fld site)
    (fld (shiftBackward4 axis site))

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

physicalFibreSumScale : ∀ coefficient fld axis transverse →
  physicalFibreSum (scaleSiteField coefficient fld) axis transverse
  ≡ coefficient * physicalFibreSum fld axis transverse
physicalFibreSumScale coefficient fld axis transverse =
  DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
    coefficient
    (allCyclicIndices side4)
    (λ coordinate → fld (insertAxis axis coordinate transverse))

quarterAddRaw : ∀ a b → quarter * (a + b) ≡ quarter * a + quarter * b
quarterAddRaw = ℚRing.solve-∀

quarterScaleRaw : ∀ c a → quarter * (c * a) ≡ c * (quarter * a)
quarterScaleRaw = ℚRing.solve-∀

axisAverageAdd : ∀ left right axis site →
  axisAverage4 (addSiteField left right) axis site
  ≡ addSiteField (axisAverage4 left axis) (axisAverage4 right axis) site
axisAverageAdd left right axis site =
  trans
    (cong (quarter *_) (physicalFibreSumAdd
      left right axis (axisTransverse axis site)))
    (quarterAddRaw
      (physicalFibreSum left axis (axisTransverse axis site))
      (physicalFibreSum right axis (axisTransverse axis site)))

axisAverageScale : ∀ coefficient fld axis site →
  axisAverage4 (scaleSiteField coefficient fld) axis site
  ≡ scaleSiteField coefficient (axisAverage4 fld axis) site
axisAverageScale coefficient fld axis site =
  trans
    (cong (quarter *_) (physicalFibreSumScale
      coefficient fld axis (axisTransverse axis site)))
    (quarterScaleRaw coefficient
      (physicalFibreSum fld axis (axisTransverse axis site)))

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

average0Scale : ∀ coefficient fld site →
  average0 (scaleSiteField coefficient fld) site
  ≡ scaleSiteField coefficient (average0 fld) site
average0Scale coefficient fld = axisAverageScale coefficient fld zeroᵢ

average01Scale : ∀ coefficient fld site →
  average01 (scaleSiteField coefficient fld) site
  ≡ scaleSiteField coefficient (average01 fld) site
average01Scale coefficient fld site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ zeroᵢ)
      (average0Scale coefficient fld) site)
    (axisAverageScale coefficient (average0 fld)
      (sucᵢ zeroᵢ) site)

average012Scale : ∀ coefficient fld site →
  average012 (scaleSiteField coefficient fld) site
  ≡ scaleSiteField coefficient (average012 fld) site
average012Scale coefficient fld site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ zeroᵢ))
      (average01Scale coefficient fld) site)
    (axisAverageScale coefficient (average01 fld)
      (sucᵢ (sucᵢ zeroᵢ)) site)

average0123Scale : ∀ coefficient fld site →
  average0123 (scaleSiteField coefficient fld) site
  ≡ scaleSiteField coefficient (average0123 fld) site
average0123Scale coefficient fld site =
  trans
    (axisAverage4RespectsPointwise (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
      (average012Scale coefficient fld) site)
    (axisAverageScale coefficient (average012 fld)
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
scalarPlaneCurlAdd plane left right site =
  trans
    (cong₂ _-_
      (forwardDifferenceAdd
        (positivePlaneFirst plane) (left (positivePlaneSecond plane))
        (right (positivePlaneSecond plane)) site)
      (forwardDifferenceAdd
        (positivePlaneSecond plane) (left (positivePlaneFirst plane))
        (right (positivePlaneFirst plane)) site))
    (diffAddRaw
      (forwardDifference4 (positivePlaneFirst plane) (left (positivePlaneSecond plane)) site)
      (forwardDifference4 (positivePlaneSecond plane) (left (positivePlaneFirst plane)) site)
      (forwardDifference4 (positivePlaneFirst plane) (right (positivePlaneSecond plane)) site)
      (forwardDifference4 (positivePlaneSecond plane) (right (positivePlaneFirst plane)) site))

scalarPlaneCurlScale : ∀ coefficient plane fld site →
  scalarPlaneCurl plane (scaleScalarBond coefficient fld) site
  ≡ coefficient * scalarPlaneCurl plane fld site
scalarPlaneCurlScale coefficient plane fld site =
  trans
    (cong₂ _-_
      (forwardDifferenceScale coefficient
        (positivePlaneFirst plane) (fld (positivePlaneSecond plane)) site)
      (forwardDifferenceScale coefficient
        (positivePlaneSecond plane) (fld (positivePlaneFirst plane)) site))
    (diffScaleRaw coefficient
      (forwardDifference4 (positivePlaneFirst plane) (fld (positivePlaneSecond plane)) site)
      (forwardDifference4 (positivePlaneSecond plane) (fld (positivePlaneFirst plane)) site))

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

backwardCurlScale : ∀ coefficient axis plane fld site →
  backwardDifference4 axis
    (scalarPlaneCurl plane (scaleScalarBond coefficient fld)) site
  ≡ coefficient
    * backwardDifference4 axis (scalarPlaneCurl plane fld) site
backwardCurlScale coefficient axis plane fld site =
  trans
    (backwardDifferenceRespectsPointwise axis
      (scalarPlaneCurlScale coefficient plane fld) site)
    (backwardDifferenceScale coefficient axis
      (scalarPlaneCurl plane fld) site)

backwardCurlRespectsPointwise : ∀ axis plane {left right} →
  (∀ bondAxis site → left bondAxis site ≡ right bondAxis site) →
  ∀ site →
  backwardDifference4 axis (scalarPlaneCurl plane left) site
  ≡ backwardDifference4 axis (scalarPlaneCurl plane right) site
backwardCurlRespectsPointwise axis plane pointwise =
  backwardDifferenceRespectsPointwise axis
    (scalarPlaneCurlRespectsPointwise plane pointwise)

negAddRaw : ∀ a b → - (a + b) ≡ - a + - b
negAddRaw = ℚRing.solve-∀

negScaleRaw : ∀ c a → - (c * a) ≡ c * (- a)
negScaleRaw = ℚRing.solve-∀

mulZeroRightRaw : ∀ c → 0ℚ ≡ c * 0ℚ
mulZeroRightRaw = ℚRing.solve-∀

planeWilsonContributionAdd : ∀ plane left right axis site →
  planeWilsonContribution plane (addScalarBond left right) axis site
  ≡ planeWilsonContribution plane left axis site
    + planeWilsonContribution plane right axis site
planeWilsonContributionAdd plane01 left right zeroᵢ site =
  backwardCurlAdd axis1 plane01 left right site
planeWilsonContributionAdd plane01 left right (sucᵢ zeroᵢ) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane01 left right site))
    (negAddRaw
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 right) site))
planeWilsonContributionAdd plane01 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  refl
planeWilsonContributionAdd plane01 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  refl
planeWilsonContributionAdd plane02 left right zeroᵢ site =
  backwardCurlAdd axis2 plane02 left right site
planeWilsonContributionAdd plane02 left right (sucᵢ zeroᵢ) site =
  refl
planeWilsonContributionAdd plane02 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane02 left right site))
    (negAddRaw
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 right) site))
planeWilsonContributionAdd plane02 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  refl
planeWilsonContributionAdd plane03 left right zeroᵢ site =
  backwardCurlAdd axis3 plane03 left right site
planeWilsonContributionAdd plane03 left right (sucᵢ zeroᵢ) site =
  refl
planeWilsonContributionAdd plane03 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  refl
planeWilsonContributionAdd plane03 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis0 plane03 left right site))
    (negAddRaw
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 left) site)
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 right) site))
planeWilsonContributionAdd plane12 left right zeroᵢ site =
  refl
planeWilsonContributionAdd plane12 left right (sucᵢ zeroᵢ) site =
  backwardCurlAdd axis2 plane12 left right site
planeWilsonContributionAdd plane12 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlAdd axis1 plane12 left right site))
    (negAddRaw
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 left) site)
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 right) site))
planeWilsonContributionAdd plane12 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  refl
planeWilsonContributionAdd plane13 left right zeroᵢ site =
  refl
planeWilsonContributionAdd plane13 left right (sucᵢ zeroᵢ) site =
  backwardCurlAdd axis3 plane13 left right site
planeWilsonContributionAdd plane13 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  refl
planeWilsonContributionAdd plane13 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis1 plane13 left right site))
    (negAddRaw
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 left) site)
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 right) site))
planeWilsonContributionAdd plane23 left right zeroᵢ site =
  refl
planeWilsonContributionAdd plane23 left right (sucᵢ zeroᵢ) site =
  refl
planeWilsonContributionAdd plane23 left right (sucᵢ (sucᵢ zeroᵢ)) site =
  backwardCurlAdd axis3 plane23 left right site
planeWilsonContributionAdd plane23 left right
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlAdd axis2 plane23 left right site))
    (negAddRaw
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 left) site)
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 right) site))

planeWilsonContributionScale : ∀ coefficient plane fld axis site →
  planeWilsonContribution plane (scaleScalarBond coefficient fld) axis site
  ≡ coefficient * planeWilsonContribution plane fld axis site
planeWilsonContributionScale coefficient plane01 fld zeroᵢ site =
  backwardCurlScale coefficient axis1 plane01 fld site
planeWilsonContributionScale coefficient plane01 fld (sucᵢ zeroᵢ) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane01 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane01 fld) site))
planeWilsonContributionScale coefficient plane01 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane01 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane02 fld zeroᵢ site =
  backwardCurlScale coefficient axis2 plane02 fld site
planeWilsonContributionScale coefficient plane02 fld (sucᵢ zeroᵢ) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane02 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane02 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane02 fld) site))
planeWilsonContributionScale coefficient plane02 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane03 fld zeroᵢ site =
  backwardCurlScale coefficient axis3 plane03 fld site
planeWilsonContributionScale coefficient plane03 fld (sucᵢ zeroᵢ) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane03 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane03 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis0 plane03 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis0 (scalarPlaneCurl plane03 fld) site))
planeWilsonContributionScale coefficient plane12 fld zeroᵢ site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane12 fld (sucᵢ zeroᵢ) site =
  backwardCurlScale coefficient axis2 plane12 fld site
planeWilsonContributionScale coefficient plane12 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis1 plane12 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis1 (scalarPlaneCurl plane12 fld) site))
planeWilsonContributionScale coefficient plane12 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane13 fld zeroᵢ site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane13 fld (sucᵢ zeroᵢ) site =
  backwardCurlScale coefficient axis3 plane13 fld site
planeWilsonContributionScale coefficient plane13 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane13 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis1 plane13 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis1 (scalarPlaneCurl plane13 fld) site))
planeWilsonContributionScale coefficient plane23 fld zeroᵢ site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane23 fld (sucᵢ zeroᵢ) site =
  mulZeroRightRaw coefficient
planeWilsonContributionScale coefficient plane23 fld
    (sucᵢ (sucᵢ zeroᵢ)) site =
  backwardCurlScale coefficient axis3 plane23 fld site
planeWilsonContributionScale coefficient plane23 fld
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site =
  trans
    (cong -_ (backwardCurlScale coefficient axis2 plane23 fld site))
    (negScaleRaw coefficient
      (backwardDifference4 axis2 (scalarPlaneCurl plane23 fld) site))

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

scalarWilsonOperatorAdd : ∀ (left right : ScalarBondField4) (axis : Axis4) site →
  scalarWilsonOperator (addScalarBond left right) axis site
  ≡ scalarWilsonOperator left axis site + scalarWilsonOperator right axis site
scalarWilsonOperatorAdd left right axis site =
  trans
    (sumRationalCong positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane (addScalarBond left right) axis site)
      (λ plane → planeWilsonContribution plane left axis site + planeWilsonContribution plane right axis site)
      (λ plane → planeWilsonContributionAdd plane left right axis site))
    (sumRationalAdd positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane left axis site)
      (λ plane → planeWilsonContribution plane right axis site))

scalarWilsonOperatorScale : ∀ coefficient (fld : ScalarBondField4) (axis : Axis4) site →
  scalarWilsonOperator (scaleScalarBond coefficient fld) axis site
  ≡ coefficient * scalarWilsonOperator fld axis site
scalarWilsonOperatorScale coefficient fld axis site =
  trans
    (sumRationalCong positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane (scaleScalarBond coefficient fld) axis site)
      (λ plane → coefficient * planeWilsonContribution plane fld axis site)
      (λ plane → planeWilsonContributionScale
        coefficient plane fld axis site))
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
      coefficient positivePlaquettePlanes4
      (λ plane → planeWilsonContribution plane fld axis site))

scalarWilsonOperatorRespectsPointwise :
  ∀ {left right : ScalarBondField4} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ axis site →
  scalarWilsonOperator left axis site ≡ scalarWilsonOperator right axis site
scalarWilsonOperatorRespectsPointwise {left} {right} pointwise axis site =
  sumRationalCong positivePlaquettePlanes4
    (λ plane → planeWilsonContribution plane left axis site)
    (λ plane → planeWilsonContribution plane right axis site)
    (λ plane →
      planeWilsonContributionRespectsPointwise plane pointwise axis site)

literalWilsonOperatorAdd : ∀ (left right : PhysicalSU2Tangent4) component bond →
  literalWilsonOperator (addPhysical left right) component bond
  ≡ literalWilsonOperator left component bond
    + literalWilsonOperator right component bond
literalWilsonOperatorAdd left right component (pair site axis) =
  scalarWilsonOperatorAdd
    (componentScalarBondField left component)
    (componentScalarBondField right component)
    axis site

literalWilsonOperatorScale : ∀ coefficient (tangent : PhysicalSU2Tangent4) component bond →
  literalWilsonOperator (scalePhysical coefficient tangent) component bond
  ≡ coefficient * literalWilsonOperator tangent component bond
literalWilsonOperatorScale coefficient tangent component (pair site axis) =
  scalarWilsonOperatorScale coefficient
    (componentScalarBondField tangent component) axis site

literalWilsonOperatorRespectsPointwise :
  ∀ {left right : PhysicalSU2Tangent4} →
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

literalPeriodicDivergenceScalarAdd : ∀ (left right : ScalarBondField4) site →
  literalPeriodicDivergenceScalar (addScalarBond left right) site
  ≡ literalPeriodicDivergenceScalar left site
    + literalPeriodicDivergenceScalar right site
literalPeriodicDivergenceScalarAdd left right site =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (addSiteField (left axis) (right axis)) site)
      (λ axis → backwardDifference4 axis (left axis) site + backwardDifference4 axis (right axis) site)
      (λ axis → backwardDifferenceAdd axis
        (left axis) (right axis) site))
    (sumRationalAdd (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (left axis) site)
      (λ axis → backwardDifference4 axis (right axis) site))

literalPeriodicDivergenceScalarScale : ∀ coefficient (fld : ScalarBondField4) site →
  literalPeriodicDivergenceScalar (scaleScalarBond coefficient fld) site
  ≡ coefficient * literalPeriodicDivergenceScalar fld site
literalPeriodicDivergenceScalarScale coefficient fld site =
  trans
    (sumRationalCong (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (scaleSiteField coefficient (fld axis)) site)
      (λ axis → coefficient * backwardDifference4 axis (fld axis) site)
      (λ axis → backwardDifferenceScale coefficient axis (fld axis) site))
    (DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.sumRationalScale
      coefficient (allCyclicIndices four)
      (λ axis → backwardDifference4 axis (fld axis) site))

literalPeriodicDivergenceScalarRespectsPointwise :
  ∀ {left right : ScalarBondField4} →
  (∀ axis site → left axis site ≡ right axis site) →
  ∀ site →
  literalPeriodicDivergenceScalar left site
  ≡ literalPeriodicDivergenceScalar right site
literalPeriodicDivergenceScalarRespectsPointwise {left} {right} pointwise site =
  sumRationalCong (allCyclicIndices four)
    (λ axis → backwardDifference4 axis (left axis) site)
    (λ axis → backwardDifference4 axis (right axis) site)
    (λ axis → backwardDifferenceRespectsPointwise axis
      (pointwise axis) site)

cong3 :
  ∀ {A B C D : Set} {f : A → B → C → D}
    {a₁ a₂ : A} {b₁ b₂ : B} {c₁ c₂ : C} →
  a₁ ≡ a₂ → b₁ ≡ b₂ → c₁ ≡ c₂ →
  f a₁ b₁ c₁ ≡ f a₂ b₂ c₂
cong3 refl refl refl = refl

literalPeriodicDivergenceAdd : ∀ left right site →
  literalPeriodicDivergence (addPhysical left right) site
  ≡ addLie3 (literalPeriodicDivergence left site)
      (literalPeriodicDivergence right site)
literalPeriodicDivergenceAdd left right site =
  cong3 {f = lie3}
    (literalPeriodicDivergenceScalarAdd
      (componentScalarBondField left component1)
      (componentScalarBondField right component1) site)
    (literalPeriodicDivergenceScalarAdd
      (componentScalarBondField left component2)
      (componentScalarBondField right component2) site)
    (literalPeriodicDivergenceScalarAdd
      (componentScalarBondField left component3)
      (componentScalarBondField right component3) site)

literalPeriodicDivergenceScale : ∀ coefficient tangent site →
  literalPeriodicDivergence (scalePhysical coefficient tangent) site
  ≡ scaleLie3 coefficient (literalPeriodicDivergence tangent site)
literalPeriodicDivergenceScale coefficient tangent site =
  cong3 {f = lie3}
    (literalPeriodicDivergenceScalarScale coefficient
      (componentScalarBondField tangent component1) site)
    (literalPeriodicDivergenceScalarScale coefficient
      (componentScalarBondField tangent component2) site)
    (literalPeriodicDivergenceScalarScale coefficient
      (componentScalarBondField tangent component3) site)

literalPeriodicDivergenceRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ site →
  literalPeriodicDivergence left site ≡ literalPeriodicDivergence right site
literalPeriodicDivergenceRespectsPointwise pointwise site =
  cong3 {f = lie3}
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
    (negAddRaw
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (left current))
        site)
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (right current))
        site))

literalNegativeForwardGradientScale : ∀ coefficient fld component bond →
  literalNegativeForwardGradient (scaleLie3Field coefficient fld) component bond
  ≡ coefficient * literalNegativeForwardGradient fld component bond
literalNegativeForwardGradientScale coefficient fld component (pair site axis) =
  trans
    (cong -_
      (trans
        (forwardDifferenceRespectsPointwise axis
          (λ current → lie3ComponentScale coefficient component (fld current))
          site)
        (forwardDifferenceScale coefficient axis
          (λ current →
            DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
              component (fld current))
          site)))
    (negScaleRaw coefficient
      (forwardDifference4 axis
        (λ current →
          DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact.lie3Component
            component (fld current))
        site))

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

threePairSumRearrangeRaw : ∀ a1 b1 a2 b2 a3 b3 →
  (a1 + b1) + ((a2 + b2) + (a3 + b3)) ≡ (a1 + (a2 + a3)) + (b1 + (b2 + b3))
threePairSumRearrangeRaw = ℚRing.solve-∀

threeScaleFactorRaw : ∀ c a1 a2 a3 →
  c * a1 + (c * a2 + c * a3) ≡ c * (a1 + (a2 + a3))
threeScaleFactorRaw = ℚRing.solve-∀

zeroMulRightRaw : ∀ x → 0ℚ * x ≡ 0ℚ
zeroMulRightRaw = ℚRing.solve-∀

mulCommRaw : ∀ a b → a * b ≡ b * a
mulCommRaw = ℚRing.solve-∀

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
        (threePairSumRearrangeRaw
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
        (threeScaleFactorRaw
          coefficient
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
configuredGaugeFixedMatrixRespectsPointwise {left} {right} pointwise component bond =
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
      {left = zeroPhysical}
      {right = scalePhysical 0ℚ zeroPhysical}
      (λ current currentBond → refl)
      component bond)
    (trans
      (configuredGaugeFixedMatrixScale 0ℚ zeroPhysical component bond)
      (zeroMulRightRaw (configuredGaugeFixedMatrix zeroPhysical component bond)))

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
    (cong (_+_ (configuredGaugeFixedMatrix (term value) component bond))
      (configuredGaugeFixedMatrixSum values term component bond))

basisExpansionPointwise : ∀ (tangent : PhysicalSU2Tangent4) (component : SU2Component) bond →
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
          delta
            physicalFiniteRationalCoordinates
            (pair component bond) column
          * tangentToCoordinateVector tangent column)
        (λ column →
          mulCommRaw
            (tangentToCoordinateVector tangent column)
            (coordinateBasisTangent column component bond)))
      (deltaActsAsIdentity
        physicalFiniteRationalCoordinates
        (tangentToCoordinateVector tangent)
        (pair component bond)))

configuredMatrixActsExactly : ∀ (tangent : PhysicalSU2Tangent4) (row : PhysicalSU2Coordinate4) →
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
      (λ column →
        mulCommRaw
          (configuredGaugeFixedMatrix (coordinateBasisTangent column) component bond)
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
          {left =
            sumPhysical
              (coordinates physicalFiniteRationalCoordinates)
              (λ column →
                scalePhysical
                  (tangentToCoordinateVector tangent column)
                  (coordinateBasisTangent column))}
          {right = tangent}
          (basisExpansionPointwise tangent)
          component bond)))

literalConfiguredMatrixActionCertificate :
  ConfiguredMatrixActionCertificate
literalConfiguredMatrixActionCertificate = record
  { configuredMatrixActsExactly =
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
