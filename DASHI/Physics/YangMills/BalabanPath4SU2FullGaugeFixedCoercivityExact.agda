module DASHI.Physics.YangMills.BalabanPath4SU2FullGaugeFixedCoercivityExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational using (ℚ; 0ℚ; _+_; _-_; _*_; _≤_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier using
  (axisTransverse; physicalBlockSites)
open import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact using
  (SiteField; sumRational; sumRationalCong)
open import DASHI.Physics.YangMills.BalabanFiniteSumFubiniExact using
  (sumRationalZero)
open import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact
open import DASHI.Physics.YangMills.BalabanPath4PhysicalMartingaleOrthogonalityExact
  using (FieldEqual; subtractField)
open import DASHI.Physics.YangMills.BalabanPath4PhysicalVarianceDecompositionExact
  using (globalNormSq)
open import DASHI.Physics.YangMills.BalabanPath4BondHodgeCoercivityExact
  using (RationalBondField4; bondComponent; bondNormSq)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicReindexingExact
  using (shiftForward4; forwardDifference4; siteSum4)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicVectorCalculusExact
  using (siteSum4Cong)
open import DASHI.Physics.YangMills.BalabanConfiguredSide4PeriodicHodgeExact
  using
    ( forwardDerivativeEnergy
    ; componentPeriodicDifferenceEnergy
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using
    ( componentScalarBondField
    ; physicalPeriodicReferenceDifferenceEnergy
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2CompleteGaugeFixedHessianExact
  using (completeLiteralGaugeFixedHessianPeriodicDecompositionExact)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
open import DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact
open import DASHI.Physics.YangMills.BalabanPath4SU2CoarsePenaltyExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using (gaugeFixedHessianQuadraticForm; blockAverageNormSq)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using (configuredPathCoercivityConstant)

------------------------------------------------------------------------
-- A fld fixed by the axis conditional expectation is translation invariant
-- along that axis.  This turns the fully averaged part into an exact zero mode
-- of every forward derivative.
------------------------------------------------------------------------

axisTransverseShiftForward : ∀ axis site →
  axisTransverse axis (shiftForward4 axis site) ≡ axisTransverse axis site
axisTransverseShiftForward zeroᵢ (pair (pair x0 x1) (pair x2 x3)) = refl
axisTransverseShiftForward (sucᵢ zeroᵢ)
  (pair (pair x0 x1) (pair x2 x3)) = refl
axisTransverseShiftForward (sucᵢ (sucᵢ zeroᵢ))
  (pair (pair x0 x1) (pair x2 x3)) = refl
axisTransverseShiftForward (sucᵢ (sucᵢ (sucᵢ zeroᵢ)))
  (pair (pair x0 x1) (pair x2 x3)) = refl

axisFixedImpliesShiftInvariant : ∀ axis fld →
  FieldEqual (axisAverage4 fld axis) fld →
  ∀ site → fld (shiftForward4 axis site) ≡ fld site
axisFixedImpliesShiftInvariant axis fld fixed site =
  trans
    (sym (fixed (shiftForward4 axis site)))
    (trans
      (cong
        (λ transverse → quarter *
          DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact.physicalFibreSum
            fld axis transverse)
        (axisTransverseShiftForward axis site))
      (fixed site))

average0123ShiftInvariant : ∀ fld axis site →
  average0123 fld (shiftForward4 axis site) ≡ average0123 fld site
average0123ShiftInvariant fld axis =
  axisFixedImpliesShiftInvariant axis (average0123 fld)
    (average0123Fixed fld axis)

subDiffCancelRaw : ∀ a b c → (a - c) - (b - c) ≡ a - b
subDiffCancelRaw = ℚRing.solve-∀

average0123ForwardDifferenceZero : ∀ fld axis site →
  forwardDifference4 axis (average0123 fld) site ≡ 0ℚ
average0123ForwardDifferenceZero fld axis site =
  trans
    (cong (λ u → u - average0123 fld site)
      (average0123ShiftInvariant fld axis site))
    (subSelfZeroRaw (average0123 fld site))

forwardDifferenceResidualExact : ∀ fld axis site →
  forwardDifference4 axis
    (subtractField fld (average0123 fld)) site
  ≡ forwardDifference4 axis fld site
forwardDifferenceResidualExact fld axis site =
  trans
    (cong
      (λ u → (fld (shiftForward4 axis site) - u) - (fld site - average0123 fld site))
      (average0123ShiftInvariant fld axis site))
    (subDiffCancelRaw (fld (shiftForward4 axis site)) (fld site) (average0123 fld site))

forwardDerivativeEnergyResidualExact : ∀ fld axis →
  forwardDerivativeEnergy axis
    (subtractField fld (average0123 fld))
  ≡ forwardDerivativeEnergy axis fld
forwardDerivativeEnergyResidualExact fld axis =
  siteSum4Cong
    (λ site →
      forwardDifference4 axis (subtractField fld (average0123 fld)) site
      * forwardDifference4 axis (subtractField fld (average0123 fld)) site)
    (λ site →
      forwardDifference4 axis fld site * forwardDifference4 axis fld site)
    (λ site →
      cong₂ _*_
        (forwardDifferenceResidualExact fld axis site)
        (forwardDifferenceResidualExact fld axis site))

scalarResidualBondField : RationalBondField4 → RationalBondField4
scalarResidualBondField fld (pair site axis) =
  fld (pair site axis) - average0123 (bondComponent fld axis) site

componentPeriodicDifferenceResidualExact : (fld : RationalBondField4) →
  componentPeriodicDifferenceEnergy (bondComponent (scalarResidualBondField fld))
  ≡ componentPeriodicDifferenceEnergy (bondComponent fld)
componentPeriodicDifferenceResidualExact fld =
  sumRationalCong
    (allCyclicIndices four)
    (λ componentAxis →
      sumRational (allCyclicIndices four) (λ derivativeAxis →
        forwardDerivativeEnergy derivativeAxis
          (bondComponent (scalarResidualBondField fld) componentAxis)))
    (λ componentAxis →
      sumRational (allCyclicIndices four) (λ derivativeAxis →
        forwardDerivativeEnergy derivativeAxis (bondComponent fld componentAxis)))
    (λ componentAxis →
      sumRationalCong
        (allCyclicIndices four)
        (λ derivativeAxis →
          forwardDerivativeEnergy derivativeAxis
            (subtractField (bondComponent fld componentAxis)
              (average0123 (bondComponent fld componentAxis))))
        (λ derivativeAxis →
          forwardDerivativeEnergy derivativeAxis (bondComponent fld componentAxis))
        (λ derivativeAxis →
          forwardDerivativeEnergyResidualExact
            (bondComponent fld componentAxis) derivativeAxis))

physicalPeriodicDifferenceResidualExact : (tangent : PhysicalSU2Tangent4) →
  physicalPeriodicReferenceDifferenceEnergy (fineFluctuation tangent)
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
physicalPeriodicDifferenceResidualExact tangent =
  cong₂ _+_
    (componentPeriodicDifferenceResidualExact (tangent component1))
    (cong₂ _+_
      (componentPeriodicDifferenceResidualExact (tangent component2))
      (componentPeriodicDifferenceResidualExact (tangent component3)))

------------------------------------------------------------------------
-- The residual projection itself is pointwise zero after applying Q, hence its
-- coarse penalty vanishes as a literal finite fold.
------------------------------------------------------------------------

fineProjectionResidualPointwiseZero : ∀ (tangent : PhysicalSU2Tangent4) (component : SU2Component) site axis →
  fineProjection (fineFluctuation tangent) component (pair site axis) ≡ 0ℚ
fineProjectionResidualPointwiseZero tangent component site axis =
  fineFluctuationAverageZero tangent component axis site

globalNormPointwiseZero : (fld : SiteField side4) →
  (∀ site → fld site ≡ 0ℚ) → globalNormSq fld ≡ 0ℚ
globalNormPointwiseZero fld fieldZero =
  trans
    (sumRationalCong
      (physicalBlockSites side4)
      (λ site → fld site * fld site)
      (λ _ → 0ℚ)
      (λ site →
        trans
          (cong₂ _*_ (fieldZero site) (fieldZero site))
          refl))
    (sumRationalZero (physicalBlockSites side4))

bondNormPointwiseZero : (fld : RationalBondField4) →
  (∀ axis site → fld (pair site axis) ≡ 0ℚ) → bondNormSq fld ≡ 0ℚ
bondNormPointwiseZero fld fieldZero =
  trans
    (sumRationalCong
      (allCyclicIndices four)
      (λ axis → globalNormSq (bondComponent fld axis))
      (λ _ → 0ℚ)
      (λ axis → globalNormPointwiseZero
        (bondComponent fld axis) (fieldZero axis)))
    (sumRationalZero (allCyclicIndices four))

physicalNormPointwiseZero : (tangent : PhysicalSU2Tangent4) →
  (∀ component site axis → tangent component (pair site axis) ≡ 0ℚ) →
  physicalUnweightedNormSq tangent ≡ 0ℚ
physicalNormPointwiseZero tangent tangentZero =
  trans
    (cong₂ _+_
      (bondNormPointwiseZero (tangent component1)
        (λ axis site → tangentZero component1 site axis))
      (cong₂ _+_
        (bondNormPointwiseZero (tangent component2)
          (λ axis site → tangentZero component2 site axis))
        (bondNormPointwiseZero (tangent component3)
          (λ axis site → tangentZero component3 site axis))))
    refl

fineProjectionResidualNormZero : ∀ tangent →
  physicalUnweightedNormSq (fineProjection (fineFluctuation tangent)) ≡ 0ℚ
fineProjectionResidualNormZero tangent =
  physicalNormPointwiseZero
    (fineProjection (fineFluctuation tangent))
    (fineProjectionResidualPointwiseZero tangent)

residualBlockPenaltyZero : ∀ tangent →
  blockAverageNormSq concreteGaugeFixedHessianData (fineFluctuation tangent)
  ≡ 0ℚ
residualBlockPenaltyZero tangent =
  trans
    (coarsePenaltyNormMatchesProjection (fineFluctuation tangent))
    (fineProjectionResidualNormZero tangent)

blockPenaltyMatchesConcreteCoarseNorm : ∀ tangent →
  blockAverageNormSq concreteGaugeFixedHessianData tangent
  ≡ concreteCoarseInner
      (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
blockPenaltyMatchesConcreteCoarseNorm tangent = refl

------------------------------------------------------------------------
-- Full gauge-fixed energy equals residual gauge-fixed energy plus the coarse
-- penalty, so the configured 1/16 coercivity is unconditional on all fields.
------------------------------------------------------------------------

addZeroRightRaw : ∀ x → x + 0ℚ ≡ x
addZeroRightRaw = ℚRing.solve-∀

residualGaugeFixedEqualsPeriodicDifference : ∀ tangent →
  gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
  ≡ physicalPeriodicReferenceDifferenceEnergy (fineFluctuation tangent)
residualGaugeFixedEqualsPeriodicDifference tangent =
  trans
    (completeLiteralGaugeFixedHessianPeriodicDecompositionExact
      concreteLiteralCoarseBlockData (fineFluctuation tangent))
    (trans
      (cong (_+_ (physicalPeriodicReferenceDifferenceEnergy (fineFluctuation tangent)))
        (residualBlockPenaltyZero tangent))
      (addZeroRightRaw (physicalPeriodicReferenceDifferenceEnergy (fineFluctuation tangent))))

fullGaugeFixedResidualDecompositionExact : ∀ tangent →
  gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
  ≡ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
    + concreteCoarseInner
        (literalBlockAverageQ tangent) (literalBlockAverageQ tangent)
fullGaugeFixedResidualDecompositionExact tangent =
  trans
    (completeLiteralGaugeFixedHessianPeriodicDecompositionExact
      concreteLiteralCoarseBlockData tangent)
    (trans
      (cong₂ _+_
        (sym (physicalPeriodicDifferenceResidualExact tangent))
        (blockPenaltyMatchesConcreteCoarseNorm tangent))
      (cong
        (λ u → u + concreteCoarseInner (literalBlockAverageQ tangent) (literalBlockAverageQ tangent))
        (sym (residualGaugeFixedEqualsPeriodicDifference tangent))))

fullGaugeFixedCoercivity : ∀ tangent →
  configuredPathCoercivityConstant * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
fullGaugeFixedCoercivity tangent =
  subst
    (λ right →
      configuredPathCoercivityConstant * physicalUnweightedNormSq tangent ≤ right)
    (sym (fullGaugeFixedResidualDecompositionExact tangent))
    (coarsePenalizedFluctuationCoercivity tangent)

averageZeroModeKernelLevel : ProofLevel
averageZeroModeKernelLevel = machineChecked

periodicDifferenceResidualInvarianceLevel : ProofLevel
periodicDifferenceResidualInvarianceLevel = machineChecked

fullGaugeFixedResidualDecompositionLevel : ProofLevel
fullGaugeFixedResidualDecompositionLevel = machineChecked

fullGaugeFixedCoercivityLevel : ProofLevel
fullGaugeFixedCoercivityLevel = machineChecked
