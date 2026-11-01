module DASHI.Physics.YangMills.BalabanClayT3LiteralPhysicalCoercivityProducerExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPath4SU2PhysicalTangentExact
open import DASHI.Physics.YangMills.BalabanSU2GaugeFixedHessianQuadraticExact
  using (gaugeFixedHessianQuadraticForm; gaugeFixingNormSq; blockAverageNormSq)
open import DASHI.Physics.YangMills.BalabanPath4SU2ConcreteCoarseBlockExact
  using
    ( concreteGaugeFixedHessianData
    ; literalBlockAverageQ
    ; concreteCoarseInner
    )
open import DASHI.Physics.YangMills.BalabanPath4SU2CoarseFineSplittingExact
  using (fineFluctuation)
open import DASHI.Physics.YangMills.BalabanPath4SU2PeriodicHodgeProducerExact
  using (physicalPeriodicReferenceDifferenceEnergy)
open import DASHI.Physics.YangMills.BalabanConfiguredRGSide4Certificate
  using (configuredPathCoercivityConstant)
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact
  using (twoℚ; fourℚ)
import DASHI.Physics.YangMills.BalabanPath4SU2FullGaugeFixedCoercivityExact as Full
import DASHI.Physics.YangMills.BalabanPath4SU2LiteralPlaquetteLiftExact as Wilson
import DASHI.Physics.YangMills.BalabanPath4SU2LiteralDivergenceHessianInstanceExact as Divergence
import DASHI.Physics.YangMills.BalabanBoolean4PatchExtensionsExact as Patch

------------------------------------------------------------------------
-- Literature:
--
-- T. Balaban, "Propagators and Renormalization Transformations for Lattice
-- Gauge Theories. I", Communications in Mathematical Physics 95 (1984),
-- 17--40. DOI: 10.1007/BF01215757
--
-- T. Balaban, "Propagators and Renormalization Transformations for Lattice
-- Gauge Theories. II", Communications in Mathematical Physics 96 (1984),
-- 223--250. DOI: 10.1007/BF01240221
--
-- E. V. Haynsworth, "Determination of the inertia of a partitioned Hermitian
-- matrix", Linear Algebra and its Applications 1 (1968), 73--81.
-- DOI: 10.1016/0024-3795(68)90050-5
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Literal configured-side reference operator.
------------------------------------------------------------------------

literalReferenceFluctuationHessianDefinition : ∀ tangent →
  gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
  ≡ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
    + concreteCoarseInner
      (literalBlockAverageQ tangent)
      (literalBlockAverageQ tangent)
literalReferenceFluctuationHessianDefinition =
  Full.fullGaugeFixedResidualDecompositionExact

literalWilsonHessianEqualsCurlEnergy : ∀ tangent →
  Wilson.literalWilsonHessianPositivePlaneFold tangent
  ≡ Wilson.literalDiscreteCurlEnergy tangent
literalWilsonHessianEqualsCurlEnergy =
  Wilson.literalWilsonHessianEqualsCurlEnergy

literalGaugeFixingEqualsDivergenceEnergy :
  ∀ {Coarse}
    (dataSet : Divergence.LiteralNonDivergenceHessianData Coarse)
    tangent →
  gaugeFixingNormSq
    (Divergence.literalGaugeFixedHessianQuadraticData dataSet) tangent
  ≡ Divergence.literalGaugeFixingEnergy tangent
literalGaugeFixingEqualsDivergenceEnergy =
  Divergence.literalGaugeFixingNormSqExact

literalBlockPenaltyEqualsConstraintEnergy : ∀ tangent →
  blockAverageNormSq concreteGaugeFixedHessianData tangent
  ≡ concreteCoarseInner
      (literalBlockAverageQ tangent)
      (literalBlockAverageQ tangent)
literalBlockPenaltyEqualsConstraintEnergy =
  Full.blockPenaltyMatchesConcreteCoarseNorm

discreteCurlDivergenceHodgeIdentity : ∀ tangent →
  gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData
      (fineFluctuation tangent)
  ≡ physicalPeriodicReferenceDifferenceEnergy
      (fineFluctuation tangent)
discreteCurlDivergenceHodgeIdentity =
  Full.residualGaugeFixedEqualsPeriodicDifference

referenceWilsonGaugeEnergyMatchesDifferenceEnergy : ∀ tangent →
  physicalPeriodicReferenceDifferenceEnergy
    (fineFluctuation tangent)
  ≡ physicalPeriodicReferenceDifferenceEnergy tangent
referenceWilsonGaugeEnergyMatchesDifferenceEnergy =
  Full.physicalPeriodicDifferenceResidualExact

bulkReferenceFluctuationCoerciveLiteral : ∀ tangent →
  configuredPathCoercivityConstant
    * physicalUnweightedNormSq tangent
  ≤ gaugeFixedHessianQuadraticForm concreteGaugeFixedHessianData tangent
bulkReferenceFluctuationCoerciveLiteral =
  Full.fullGaugeFixedCoercivity

------------------------------------------------------------------------
-- Canonical local patch retracts.
------------------------------------------------------------------------

boundaryRestrictionAfterExtension : ∀ face →
  Patch.restrictFace0 (Patch.extendFace0 face) ≡ face
boundaryRestrictionAfterExtension = Patch.restrictFaceAfterExtend

interfaceRestrictionAfterExtension : ∀ face →
  Patch.restrictFace0 (Patch.extendFace0 face) ≡ face
interfaceRestrictionAfterExtension = Patch.restrictFaceAfterExtend

cornerRestrictionAfterExtension : ∀ corner →
  Patch.restrictCorner01 (Patch.extendCorner01 corner) ≡ corner
cornerRestrictionAfterExtension = Patch.restrictCornerAfterExtend

nestedRestrictionAfterExtension : ∀ corner →
  Patch.restrictCorner01 (Patch.extendCorner01 corner) ≡ corner
nestedRestrictionAfterExtension = Patch.restrictCornerAfterExtend

boundaryExtensionEnergyComparison : ∀ face →
  Patch.edgeEnergy (Patch.extendFace0 face)
  ≡ twoℚ * Patch.faceEdgeEnergy face
boundaryExtensionEnergyComparison = Patch.faceEnergyIdentity

interfaceExtensionEnergyComparison : ∀ face →
  Patch.edgeEnergy (Patch.extendFace0 face)
  ≡ twoℚ * Patch.faceEdgeEnergy face
interfaceExtensionEnergyComparison = Patch.faceEnergyIdentity

cornerExtensionEnergyComparison : ∀ corner →
  Patch.edgeEnergy (Patch.extendCorner01 corner)
  ≡ fourℚ * Patch.cornerEdgeEnergy corner
cornerExtensionEnergyComparison = Patch.cornerEnergyIdentity

nestedExtensionEnergyComparison : ∀ corner →
  Patch.edgeEnergy (Patch.extendCorner01 corner)
  ≡ fourℚ * Patch.cornerEdgeEnergy corner
nestedExtensionEnergyComparison = Patch.cornerEnergyIdentity

boundaryPatchCoerciveFromBulk : ∀ face →
  Patch.faceSum face ≡ 0ℚ →
  twoℚ * Patch.faceNormSq face
  ≤ Patch.faceEdgeEnergy face
boundaryPatchCoerciveFromBulk = Patch.facePoincare

interfacePatchCoerciveFromBulk : ∀ face →
  Patch.faceSum face ≡ 0ℚ →
  twoℚ * Patch.faceNormSq face
  ≤ Patch.faceEdgeEnergy face
interfacePatchCoerciveFromBulk = Patch.facePoincare

cornerPatchCoerciveFromBulk : ∀ corner →
  Patch.cornerSum corner ≡ 0ℚ →
  twoℚ * Patch.cornerNormSq corner
  ≤ Patch.cornerEdgeEnergy corner
cornerPatchCoerciveFromBulk = Patch.cornerPoincare

nestedPatchCoerciveFromBulk : ∀ corner →
  Patch.cornerSum corner ≡ 0ℚ →
  twoℚ * Patch.cornerNormSq corner
  ≤ Patch.cornerEdgeEnergy corner
nestedPatchCoerciveFromBulk = Patch.cornerPoincare

------------------------------------------------------------------------
-- Exact gauge-kernel reduction.
------------------------------------------------------------------------

record LiteralGaugeKernelData (Index State Gauge : Set) : Set₁ where
  field
    referenceHessian : Index → State → State
    gaugeMode : Index → Gauge → State
    zeroState : State

    GaugeFixedTangent ConstraintTangent : Index → State → Set

    referenceHessianGaugeModeZero : ∀ index omega →
      referenceHessian index (gaugeMode index omega) ≡ zeroState

    referenceHessianKernelOnlyGaugeModes : ∀ index state →
      referenceHessian index state ≡ zeroState →
      Σ Gauge (λ omega → state ≡ gaugeMode index omega)

    gaugeModeExcludedOnFixedConstraintSlice :
      ∀ index state omega →
      GaugeFixedTangent index state →
      ConstraintTangent index state →
      state ≡ gaugeMode index omega →
      state ≡ zeroState

open LiteralGaugeKernelData public

gaugeFixedConstraintSliceKernelTrivial :
  ∀ {Index State Gauge}
    (dataSet : LiteralGaugeKernelData Index State Gauge)
    index state →
  GaugeFixedTangent dataSet index state →
  ConstraintTangent dataSet index state →
  referenceHessian dataSet index state ≡ zeroState dataSet →
  state ≡ zeroState dataSet
gaugeFixedConstraintSliceKernelTrivial dataSet index state fixed constrained kernel
  with referenceHessianKernelOnlyGaugeModes dataSet index state kernel
... | omega , stateIsGauge =
  gaugeModeExcludedOnFixedConstraintSlice dataSet index state omega
    fixed constrained stateIsGauge

------------------------------------------------------------------------
-- Five-term relative-Hessian theorem.
------------------------------------------------------------------------

record LiteralPhysicalHessianPerturbationData
    (Index State Bound : Set) : Set₁ where
  field
    referenceEnergy physicalEnergy remainderEnergy normSq :
      Index → State → Bound
    curvatureRemainder transportRemainder chartRemainder
      gaugeRemainder constraintRemainder : Index → State → Bound

    add scale : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    zero one half cReference cPhysical : Bound
    εCurvature εTransport εChart εGauge εConstraint εTotal : Bound

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left left′ right right′} →
      LessEqual left left′ → LessEqual right right′ →
      LessEqual (add left right) (add left′ right′)
    addRightCancel : ∀ {left right common} →
      LessEqual (add left common) (add right common) →
      LessEqual left right

    physicalFluctuationHessianSplitLiteral : ∀ index state →
      LessEqual (referenceEnergy index state)
        (add (physicalEnergy index state) (remainderEnergy index state))

    backgroundHessianRemainderSplitLiteral : ∀ index state →
      LessEqual (remainderEnergy index state)
        (add (curvatureRemainder index state)
          (add (transportRemainder index state)
            (add (chartRemainder index state)
              (add (gaugeRemainder index state)
                (constraintRemainder index state)))))

    curvatureRemainderRelativeBound : ∀ index state →
      LessEqual (curvatureRemainder index state)
        (scale εCurvature (normSq index state))
    transportRemainderRelativeBound : ∀ index state →
      LessEqual (transportRemainder index state)
        (scale εTransport (normSq index state))
    chartRemainderRelativeBound : ∀ index state →
      LessEqual (chartRemainder index state)
        (scale εChart (normSq index state))
    gaugeRemainderRelativeBound : ∀ index state →
      LessEqual (gaugeRemainder index state)
        (scale εGauge (normSq index state))
    constraintRemainderRelativeBound : ∀ index state →
      LessEqual (constraintRemainder index state)
        (scale εConstraint (normSq index state))

    combineScaledRemainders : ∀ radius →
      add (scale εCurvature radius)
        (add (scale εTransport radius)
          (add (scale εChart radius)
            (add (scale εGauge radius)
              (scale εConstraint radius))))
      ≡ scale εTotal radius

    εTotalBelowHalf : LessEqual εTotal half
    scaleMonotone : ∀ {left right radius} →
      LessEqual left right →
      LessEqual (scale left radius) (scale right radius)

    referenceCoercive : ∀ index state →
      LessEqual (scale cReference (normSq index state))
        (referenceEnergy index state)

    coercivityBudget : ∀ state →
      LessEqual
        (add (scale cPhysical (normSq state))
          (scale εTotal (normSq state)))
        (scale cReference (normSq state))

open LiteralPhysicalHessianPerturbationData public

totalRelativeHessianRemainderBound :
  ∀ {Index State Bound}
    (dataSet : LiteralPhysicalHessianPerturbationData Index State Bound)
    index state →
  LessEqual dataSet
    (remainderEnergy dataSet index state)
    (scale dataSet (εTotal dataSet) (normSq dataSet index state))
totalRelativeHessianRemainderBound dataSet index state =
  transitive dataSet
    (backgroundHessianRemainderSplitLiteral dataSet index state)
    (subst
      (λ upper →
        LessEqual dataSet
          (add dataSet
            (curvatureRemainder dataSet index state)
            (add dataSet
              (transportRemainder dataSet index state)
              (add dataSet
                (chartRemainder dataSet index state)
                (add dataSet
                  (gaugeRemainder dataSet index state)
                  (constraintRemainder dataSet index state)))))
          upper)
      (combineScaledRemainders dataSet (normSq dataSet index state))
      (addMonotone dataSet
        (curvatureRemainderRelativeBound dataSet index state)
        (addMonotone dataSet
          (transportRemainderRelativeBound dataSet index state)
          (addMonotone dataSet
            (chartRemainderRelativeBound dataSet index state)
            (addMonotone dataSet
              (gaugeRemainderRelativeBound dataSet index state)
              (constraintRemainderRelativeBound dataSet index state)))))))

totalRelativeHessianRemainderBelowHalf :
  ∀ {Index State Bound}
    (dataSet : LiteralPhysicalHessianPerturbationData Index State Bound)
    index state →
  LessEqual dataSet
    (remainderEnergy dataSet index state)
    (scale dataSet (half dataSet) (normSq dataSet index state))
totalRelativeHessianRemainderBelowHalf dataSet index state =
  transitive dataSet
    (totalRelativeHessianRemainderBound dataSet index state)
    (scaleMonotone dataSet (εTotalBelowHalf dataSet))

physicalSmallFieldFluctuationCoercive :
  ∀ {Index State Bound}
    (dataSet : LiteralPhysicalHessianPerturbationData Index State Bound)
    index state →
  LessEqual dataSet
    (scale dataSet (cPhysical dataSet) (normSq dataSet index state))
    (physicalEnergy dataSet index state)
physicalSmallFieldFluctuationCoercive dataSet index state =
  addRightCancel dataSet
    (transitive dataSet
      (coercivityBudget dataSet state)
      (transitive dataSet
        (referenceCoercive dataSet index state)
        (transitive dataSet
          (physicalFluctuationHessianSplitLiteral dataSet index state)
          (addMonotone dataSet
            (reflexive dataSet (physicalEnergy dataSet index state))
            (totalRelativeHessianRemainderBound dataSet index state)))))

------------------------------------------------------------------------
-- Green and uniform Schur output.
------------------------------------------------------------------------

record PhysicalFluctuationGreenData (Index State Bound : Set) : Set₁ where
  field
    physicalHessian green : Index → State → State
    operatorNorm : (State → State) → Bound
    reciprocalCPhysical : Bound
    LessEqual : Bound → Bound → Set

    physicalFluctuationGreenLeftInverse : ∀ index state →
      green index (physicalHessian index state) ≡ state
    physicalFluctuationGreenRightInverse : ∀ index state →
      physicalHessian index (green index state) ≡ state
    physicalFluctuationGreenNormBound : ∀ index →
      LessEqual (operatorNorm (green index)) reciprocalCPhysical

open PhysicalFluctuationGreenData public

physicalFluctuationGreenExists :
  ∀ {Index State Bound} →
  PhysicalFluctuationGreenData Index State Bound →
  Index → Set
physicalFluctuationGreenExists dataSet index =
  (∀ state → green dataSet index (physicalHessian dataSet index state) ≡ state)
  × (∀ state → physicalHessian dataSet index (green dataSet index state) ≡ state)

physicalFluctuationGreenExistsProof :
  ∀ {Index State Bound}
    (dataSet : PhysicalFluctuationGreenData Index State Bound)
    index →
  physicalFluctuationGreenExists dataSet index
physicalFluctuationGreenExistsProof dataSet index =
  Data.Product._,_
    (physicalFluctuationGreenLeftInverse dataSet index)
    (physicalFluctuationGreenRightInverse dataSet index)

record PhysicalUniformFluctuationSchurFamily
    (Index State Bound : Set) : Set₁ where
  field
    coercivityData :
      LiteralPhysicalHessianPerturbationData Index State Bound
    greenData : PhysicalFluctuationGreenData Index State Bound

open PhysicalUniformFluctuationSchurFamily public

physicalUniformFluctuationSchurFamily :
  ∀ {Index State Bound} →
  LiteralPhysicalHessianPerturbationData Index State Bound →
  PhysicalFluctuationGreenData Index State Bound →
  PhysicalUniformFluctuationSchurFamily Index State Bound
physicalUniformFluctuationSchurFamily coercivity green = record
  { coercivityData = coercivity
  ; greenData = green
  }

literalReferenceHodgeProducerLevel : ProofLevel
literalReferenceHodgeProducerLevel = machineChecked

literalPatchTransferProducerLevel : ProofLevel
literalPatchTransferProducerLevel = machineChecked

literalGaugeKernelReductionLevel : ProofLevel
literalGaugeKernelReductionLevel = machineChecked

fiveTermRelativeHessianCombinationLevel : ProofLevel
fiveTermRelativeHessianCombinationLevel = machineChecked

physicalSmallFieldCoercivityProducerLevel : ProofLevel
physicalSmallFieldCoercivityProducerLevel = machineChecked

literalFiveComponentEstimateInputsLevel : ProofLevel
literalFiveComponentEstimateInputsLevel = conditional
