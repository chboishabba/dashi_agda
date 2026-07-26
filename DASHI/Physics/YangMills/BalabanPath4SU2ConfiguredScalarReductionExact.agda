module DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredScalarReductionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
  using (side4; average0123)
open import DASHI.Physics.YangMills.BalabanPath4PlaquetteOrientationExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using
    ( ScalarBondField4
    ; literalPeriodicDivergenceScalar
    ; literalNegativeForwardGradientScalar
    ; backwardForwardDifferenceCommutes
    ; axis0
    ; axis1
    ; axis2
    ; axis3
    )
open import DASHI.Physics.YangMills.BalabanConfiguredSide4ScalarWilsonOperatorExact
  using (scalarPlaneCurl; scalarWilsonOperator)
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (componentScalarBondField)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConfiguredMatrixActionExact
  using
    ( literalGaugePenalty
    ; configuredGaugeFixedMatrixPointwise
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using (fineProjection)

subtractSiteField : SiteField side4 → SiteField side4 → SiteField side4
subtractSiteField left right site = left site - right site

backwardDifferenceSubtract : ∀ axis left right site →
  backwardDifference4 axis (subtractSiteField left right) site
  ≡ backwardDifference4 axis left site
    - backwardDifference4 axis right site
backwardDifferenceSubtract axis left right site =
  ℚRing.solve-∀
    (left site) (right site)
    (left (shiftBackward4 axis site))
    (right (shiftBackward4 axis site))

backwardPlaneCurlExpand : ∀ backwardAxis plane field site →
  backwardDifference4 backwardAxis (scalarPlaneCurl plane field) site
  ≡ backwardDifference4 backwardAxis
      (forwardDifference4 (positivePlaneFirst plane)
        (field (positivePlaneSecond plane))) site
    - backwardDifference4 backwardAxis
      (forwardDifference4 (positivePlaneSecond plane)
        (field (positivePlaneFirst plane))) site
backwardPlaneCurlExpand backwardAxis plane field =
  backwardDifferenceSubtract backwardAxis
    (forwardDifference4 (positivePlaneFirst plane)
      (field (positivePlaneSecond plane)))
    (forwardDifference4 (positivePlaneSecond plane)
      (field (positivePlaneFirst plane)))

scalarGaugePenalty : ScalarBondField4 → ScalarBondField4
scalarGaugePenalty field =
  literalNegativeForwardGradientScalar
    (literalPeriodicDivergenceScalar field)

scalarForwardBackwardLaplacian : ScalarBondField4 → ScalarBondField4
scalarForwardBackwardLaplacian field componentAxis site =
  - sumRational (allCyclicIndices four)
      (λ derivativeAxis →
        forwardDifference4 derivativeAxis
          (backwardDifference4 derivativeAxis (field componentAxis)) site)

scalarWilsonGaugeCollapse : ∀ field componentAxis site →
  scalarWilsonOperator field componentAxis site
    + scalarGaugePenalty field componentAxis site
  ≡ scalarForwardBackwardLaplacian field componentAxis site
scalarWilsonGaugeCollapse field zeroᵢ site
  rewrite backwardPlaneCurlExpand axis1 plane01 field site
        | backwardPlaneCurlExpand axis2 plane02 field site
        | backwardPlaneCurlExpand axis3 plane03 field site
        | backwardForwardDifferenceCommutes axis1 axis0 (field axis1) site
        | backwardForwardDifferenceCommutes axis1 axis1 (field axis0) site
        | backwardForwardDifferenceCommutes axis2 axis0 (field axis2) site
        | backwardForwardDifferenceCommutes axis2 axis2 (field axis0) site
        | backwardForwardDifferenceCommutes axis3 axis0 (field axis3) site
        | backwardForwardDifferenceCommutes axis3 axis3 (field axis0) site =
  ℚRing.solve-∀
scalarWilsonGaugeCollapse field (sucᵢ zeroᵢ) site
  rewrite backwardPlaneCurlExpand axis0 plane01 field site
        | backwardPlaneCurlExpand axis2 plane12 field site
        | backwardPlaneCurlExpand axis3 plane13 field site
        | backwardForwardDifferenceCommutes axis0 axis0 (field axis1) site
        | backwardForwardDifferenceCommutes axis0 axis1 (field axis0) site
        | backwardForwardDifferenceCommutes axis2 axis1 (field axis2) site
        | backwardForwardDifferenceCommutes axis2 axis2 (field axis1) site
        | backwardForwardDifferenceCommutes axis3 axis1 (field axis3) site
        | backwardForwardDifferenceCommutes axis3 axis3 (field axis1) site =
  ℚRing.solve-∀
scalarWilsonGaugeCollapse field (sucᵢ (sucᵢ zeroᵢ)) site
  rewrite backwardPlaneCurlExpand axis0 plane02 field site
        | backwardPlaneCurlExpand axis1 plane12 field site
        | backwardPlaneCurlExpand axis3 plane23 field site
        | backwardForwardDifferenceCommutes axis0 axis0 (field axis2) site
        | backwardForwardDifferenceCommutes axis0 axis2 (field axis0) site
        | backwardForwardDifferenceCommutes axis1 axis1 (field axis2) site
        | backwardForwardDifferenceCommutes axis1 axis2 (field axis1) site
        | backwardForwardDifferenceCommutes axis3 axis2 (field axis3) site
        | backwardForwardDifferenceCommutes axis3 axis3 (field axis2) site =
  ℚRing.solve-∀
scalarWilsonGaugeCollapse field
    (sucᵢ (sucᵢ (sucᵢ zeroᵢ))) site
  rewrite backwardPlaneCurlExpand axis0 plane03 field site
        | backwardPlaneCurlExpand axis1 plane13 field site
        | backwardPlaneCurlExpand axis2 plane23 field site
        | backwardForwardDifferenceCommutes axis0 axis0 (field axis3) site
        | backwardForwardDifferenceCommutes axis0 axis3 (field axis0) site
        | backwardForwardDifferenceCommutes axis1 axis1 (field axis3) site
        | backwardForwardDifferenceCommutes axis1 axis3 (field axis1) site
        | backwardForwardDifferenceCommutes axis2 axis2 (field axis3) site
        | backwardForwardDifferenceCommutes axis2 axis3 (field axis2) site =
  ℚRing.solve-∀

shiftBackwardAfterForward : ∀ axis site →
  shiftBackward4 axis (shiftForward4 axis site) ≡ site
shiftBackwardAfterForward zeroᵢ (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x0 = refl
shiftBackwardAfterForward (sucᵢ zeroᵢ)
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x1 = refl
shiftBackwardAfterForward (sucᵢ (sucᵢ zeroᵢ))
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x2 = refl
shiftBackwardAfterForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
    (pair (pair x0 x1) (pair x2 x3))
  rewrite previousNext4 x3 = refl

negativeForwardBackwardStencil : ∀ axis field site →
  - forwardDifference4 axis (backwardDifference4 axis field) site
  ≡ (field site + field site)
      - (field (shiftForward4 axis site)
        + field (shiftBackward4 axis site))
negativeForwardBackwardStencil axis field site
  rewrite shiftBackwardAfterForward axis site =
  ℚRing.solve-∀
    (field site)
    (field (shiftForward4 axis site))
    (field (shiftBackward4 axis site))

scalarLocalLaplacian : ScalarBondField4 → ScalarBondField4
scalarLocalLaplacian field componentAxis site =
  sumRational (allCyclicIndices four)
    (λ derivativeAxis →
      (field componentAxis site + field componentAxis site)
      - (field componentAxis (shiftForward4 derivativeAxis site)
        + field componentAxis (shiftBackward4 derivativeAxis site)))

fourTermCong : ∀ {a0 a1 a2 a3 b0 b1 b2 b3 : ℚ} →
  a0 ≡ b0 → a1 ≡ b1 → a2 ≡ b2 → a3 ≡ b3 →
  a0 + (a1 + (a2 + a3)) ≡ b0 + (b1 + (b2 + b3))
fourTermCong refl refl refl refl = refl

scalarForwardBackwardEqualsLocal : ∀ field componentAxis site →
  scalarForwardBackwardLaplacian field componentAxis site
  ≡ scalarLocalLaplacian field componentAxis site
scalarForwardBackwardEqualsLocal field componentAxis site =
  trans
    (ℚRing.solve-∀
      (forwardDifference4 axis0
        (backwardDifference4 axis0 (field componentAxis)) site)
      (forwardDifference4 axis1
        (backwardDifference4 axis1 (field componentAxis)) site)
      (forwardDifference4 axis2
        (backwardDifference4 axis2 (field componentAxis)) site)
      (forwardDifference4 axis3
        (backwardDifference4 axis3 (field componentAxis)) site))
    (trans
      (fourTermCong
        (negativeForwardBackwardStencil axis0 (field componentAxis) site)
        (negativeForwardBackwardStencil axis1 (field componentAxis) site)
        (negativeForwardBackwardStencil axis2 (field componentAxis) site)
        (negativeForwardBackwardStencil axis3 (field componentAxis) site))
      (ℚRing.solve-∀
        ((field componentAxis site + field componentAxis site)
          - (field componentAxis (shiftForward4 axis0 site)
            + field componentAxis (shiftBackward4 axis0 site)))
        ((field componentAxis site + field componentAxis site)
          - (field componentAxis (shiftForward4 axis1 site)
            + field componentAxis (shiftBackward4 axis1 site)))
        ((field componentAxis site + field componentAxis site)
          - (field componentAxis (shiftForward4 axis2 site)
            + field componentAxis (shiftBackward4 axis2 site)))
        ((field componentAxis site + field componentAxis site)
          - (field componentAxis (shiftForward4 axis3 site)
            + field componentAxis (shiftBackward4 axis3 site)))))

configuredGaugeFixedMatrixEqualsLaplacianPlusMean :
  ∀ tangent component site bondAxis →
  DASHI.Physics.YangMills.BalabanPath4SU2ConcretePropagatorExact.configuredGaugeFixedMatrix
    tangent component (pair site bondAxis)
  ≡ scalarLocalLaplacian
      (componentScalarBondField tangent component) bondAxis site
    + average0123
      (componentScalarBondField tangent component bondAxis) site
configuredGaugeFixedMatrixEqualsLaplacianPlusMean
    tangent component site bondAxis =
  trans
    (configuredGaugeFixedMatrixPointwise tangent component (pair site bondAxis))
    (trans
      (ℚRing.solve-∀
        (scalarWilsonOperator
          (componentScalarBondField tangent component) bondAxis site)
        (scalarGaugePenalty
          (componentScalarBondField tangent component) bondAxis site)
        (fineProjection tangent component (pair site bondAxis)))
      (trans
        (cong
          (λ wilsonGauge → wilsonGauge
            + fineProjection tangent component (pair site bondAxis))
          (scalarWilsonGaugeCollapse
            (componentScalarBondField tangent component) bondAxis site))
        (cong
          (λ laplacian → laplacian
            + average0123
                (componentScalarBondField tangent component bondAxis) site)
          (scalarForwardBackwardEqualsLocal
            (componentScalarBondField tangent component) bondAxis site))))

scalarWilsonGaugeOperatorHodgeLevel : ProofLevel
scalarWilsonGaugeOperatorHodgeLevel = machineChecked

configuredLaplacianPlusMeanReductionLevel : ProofLevel
configuredLaplacianPlusMeanReductionLevel = machineChecked
