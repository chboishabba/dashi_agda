module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredGreenExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (sumRational; sumRationalCong; sumRationalScale)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact using (side4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (siteSum4Cong)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (componentScalarBondField)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact
  using (configuredGaugeFixedMatrix)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredScalarReductionExact
  using (configuredGaugeFixedMatrixEqualsLaplacianPlusMean)
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenKernelComputed
  using (scalarGreenKernel)
open import DASHI.Physics.YangMills.BalabanSide4TranslationDifferenceExact
  using (subtractSite4)
open import DASHI.Physics.YangMills.BalabanSide4ScalarGreenConvolutionExact
  using
    ( scalarGreen
    ; scalarGreenAdd
    ; scalarGreenRespectsPointwise
    ; configuredSiteGreenRightInverse
    ; configuredSiteGreenLeftInverse
    )
open import DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact
open import DASHI.Physics.YangMills.BalabanPath4SU2RationalMatrixCoordinatesExact
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact
  using
    ( addPhysical
    ; scalePhysical
    ; zeroPhysical
    ; sumPhysical
    ; basisExpansionPointwise
    ; configuredMatrixActsExactly
    )

------------------------------------------------------------------------
-- Componentwise physical Green operator and two-sided inverse.
------------------------------------------------------------------------

configuredPhysicalGreen : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
configuredPhysicalGreen source component (pair site bondAxis) =
  scalarGreen (componentScalarBondField source component bondAxis) site

configuredPhysicalGreenRightInverse : ∀ source component bond →
  configuredGaugeFixedMatrix (configuredPhysicalGreen source) component bond
  ≡ source component bond
configuredPhysicalGreenRightInverse source component (pair site bondAxis) =
  trans
    (configuredGaugeFixedMatrixEqualsLaplacianPlusMean
      (configuredPhysicalGreen source) component site bondAxis)
    (configuredSiteGreenRightInverse
      (componentScalarBondField source component bondAxis) site)

configuredPhysicalGreenLeftInverse : ∀ source component bond →
  configuredPhysicalGreen (configuredGaugeFixedMatrix source) component bond
  ≡ source component bond
configuredPhysicalGreenLeftInverse source component (pair site bondAxis) =
  trans
    (scalarGreenRespectsPointwise
      (λ current →
        configuredGaugeFixedMatrixEqualsLaplacianPlusMean
          source component current bondAxis)
      site)
    (configuredSiteGreenLeftInverse
      (componentScalarBondField source component bondAxis) site)

record ConfiguredPhysicalGreenCertificate : Set₁ where
  field
    green : PhysicalSU2Tangent4 → PhysicalSU2Tangent4
    inverseLeftPointwise : ∀ tangent component bond →
      green (configuredGaugeFixedMatrix tangent) component bond
      ≡ tangent component bond
    inverseRightPointwise : ∀ tangent component bond →
      configuredGaugeFixedMatrix (green tangent) component bond
      ≡ tangent component bond

open ConfiguredPhysicalGreenCertificate public

literalConfiguredPhysicalGreenCertificate : ConfiguredPhysicalGreenCertificate
literalConfiguredPhysicalGreenCertificate = record
  { green = configuredPhysicalGreen
  ; inverseLeftPointwise = configuredPhysicalGreenLeftInverse
  ; inverseRightPointwise = configuredPhysicalGreenRightInverse
  }

------------------------------------------------------------------------
-- Rational linearity and exact matrix action of the Green operator.
------------------------------------------------------------------------

scalarGreenScale : ∀ coefficient source row →
  scalarGreen (λ site → coefficient * source site) row
  ≡ coefficient * scalarGreen source row
scalarGreenScale coefficient source row =
  trans
    (siteSum4Cong _ _ (λ column → ℚRing.solve-∀
      coefficient
      (scalarGreenKernel (subtractSite4 row column))
      (source column)))
    (sumRationalScale coefficient (physicalBlockSites side4)
      (λ column →
        scalarGreenKernel (subtractSite4 row column) * source column))

configuredPhysicalGreenAdd : ∀ left right component bond →
  configuredPhysicalGreen (addPhysical left right) component bond
  ≡ configuredPhysicalGreen left component bond
    + configuredPhysicalGreen right component bond
configuredPhysicalGreenAdd left right component (pair site bondAxis) =
  scalarGreenAdd
    (componentScalarBondField left component bondAxis)
    (componentScalarBondField right component bondAxis)
    site

configuredPhysicalGreenScale : ∀ coefficient source component bond →
  configuredPhysicalGreen (scalePhysical coefficient source) component bond
  ≡ coefficient * configuredPhysicalGreen source component bond
configuredPhysicalGreenScale coefficient source component (pair site bondAxis) =
  scalarGreenScale coefficient
    (componentScalarBondField source component bondAxis) site

configuredPhysicalGreenRespectsPointwise :
  ∀ {left right} →
  (∀ component bond → left component bond ≡ right component bond) →
  ∀ component bond →
  configuredPhysicalGreen left component bond
  ≡ configuredPhysicalGreen right component bond
configuredPhysicalGreenRespectsPointwise pointwise component
    (pair site bondAxis) =
  scalarGreenRespectsPointwise
    (λ current → pointwise component (pair current bondAxis)) site

configuredPhysicalGreenZero : ∀ component bond →
  configuredPhysicalGreen zeroPhysical component bond ≡ 0ℚ
configuredPhysicalGreenZero component bond =
  trans
    (configuredPhysicalGreenScale 0ℚ zeroPhysical component bond)
    (ℚRing.solve-∀ (configuredPhysicalGreen zeroPhysical component bond))

configuredPhysicalGreenSum :
  ∀ {Index : Set} (values : List Index)
    (term : Index → PhysicalSU2Tangent4) component bond →
  configuredPhysicalGreen (sumPhysical values term) component bond
  ≡ sumRational values
      (λ value → configuredPhysicalGreen (term value) component bond)
configuredPhysicalGreenSum [] term component bond =
  configuredPhysicalGreenZero component bond
configuredPhysicalGreenSum (value ∷ values) term component bond =
  trans
    (configuredPhysicalGreenAdd
      (term value) (sumPhysical values term) component bond)
    (cong (configuredPhysicalGreen (term value) component bond +_)
      (configuredPhysicalGreenSum values term component bond))

configuredGreenOperatorMatrix : RationalMatrix PhysicalSU2Coordinate4
configuredGreenOperatorMatrix row column =
  tangentToCoordinateVector
    (configuredPhysicalGreen (coordinateBasisTangent column)) row

configuredGreenMatrixActsExactly : ∀ tangent row →
  applyMatrix
    physicalFiniteRationalCoordinates
    configuredGreenOperatorMatrix
    (tangentToCoordinateVector tangent)
    row
  ≡ tangentToCoordinateVector (configuredPhysicalGreen tangent) row
configuredGreenMatrixActsExactly tangent (pair component bond) =
  trans
    (sumRationalCong
      (coordinates physicalFiniteRationalCoordinates)
      (λ column →
        configuredPhysicalGreen (coordinateBasisTangent column) component bond
        * tangentToCoordinateVector tangent column)
      (λ column →
        tangentToCoordinateVector tangent column
        * configuredPhysicalGreen (coordinateBasisTangent column) component bond)
      (λ column → ℚRing.solve-∀
        (configuredPhysicalGreen (coordinateBasisTangent column) component bond)
        (tangentToCoordinateVector tangent column)))
    (trans
      (sumRationalCong
        (coordinates physicalFiniteRationalCoordinates)
        (λ column →
          tangentToCoordinateVector tangent column
          * configuredPhysicalGreen (coordinateBasisTangent column) component bond)
        (λ column →
          configuredPhysicalGreen
            (scalePhysical
              (tangentToCoordinateVector tangent column)
              (coordinateBasisTangent column))
            component bond)
        (λ column →
          sym (configuredPhysicalGreenScale
            (tangentToCoordinateVector tangent column)
            (coordinateBasisTangent column)
            component bond)))
      (trans
        (sym
          (configuredPhysicalGreenSum
            (coordinates physicalFiniteRationalCoordinates)
            (λ column →
              scalePhysical
                (tangentToCoordinateVector tangent column)
                (coordinateBasisTangent column))
            component bond))
        (configuredPhysicalGreenRespectsPointwise
          (basisExpansionPointwise tangent)
          component bond)))

------------------------------------------------------------------------
-- Exact rational matrix inverse certificate.
------------------------------------------------------------------------

configuredGreenTimesOperator : ∀ row column →
  multiplyMatrix
    physicalFiniteRationalCoordinates
    configuredGreenOperatorMatrix
    configuredGaugeFixedOperatorMatrix
    row column
  ≡ delta physicalFiniteRationalCoordinates row column
configuredGreenTimesOperator (pair component bond) column =
  trans
    (configuredGreenMatrixActsExactly
      (configuredGaugeFixedMatrix (coordinateBasisTangent column))
      (pair component bond))
    (configuredPhysicalGreenLeftInverse
      (coordinateBasisTangent column) component bond)

configuredOperatorTimesGreen : ∀ row column →
  multiplyMatrix
    physicalFiniteRationalCoordinates
    configuredGaugeFixedOperatorMatrix
    configuredGreenOperatorMatrix
    row column
  ≡ delta physicalFiniteRationalCoordinates row column
configuredOperatorTimesGreen (pair component bond) column =
  trans
    (configuredMatrixActsExactly
      (configuredPhysicalGreen (coordinateBasisTangent column))
      (pair component bond))
    (configuredPhysicalGreenRightInverse
      (coordinateBasisTangent column) component bond)

configuredGaugeFixedMatrixInverseCertificate :
  RationalMatrixInverseCertificate
    physicalFiniteRationalCoordinates
    configuredGaugeFixedOperatorMatrix
configuredGaugeFixedMatrixInverseCertificate = record
  { inverseMatrix = configuredGreenOperatorMatrix
  ; inverseTimesOperator = configuredGreenTimesOperator
  ; operatorTimesInverse = configuredOperatorTimesGreen
  }

configuredPhysicalGreenTwoSidedLevel : ProofLevel
configuredPhysicalGreenTwoSidedLevel = machineChecked

configuredGreenMatrixActionLevel : ProofLevel
configuredGreenMatrixActionLevel = machineChecked

configuredGreenMatrixInverseProductLevel : ProofLevel
configuredGreenMatrixInverseProductLevel = machineChecked

-- The remaining finite propagator obligation is the quantitative norm estimate
-- for this explicit inverse.  The inverse itself and both products are concrete.
configuredGreenNormProducerLevel : ProofLevel
configuredGreenNormProducerLevel = conditional
