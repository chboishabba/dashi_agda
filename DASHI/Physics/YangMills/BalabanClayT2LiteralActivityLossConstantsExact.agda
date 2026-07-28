module DASHI.Physics.YangMills.BalabanClayT2LiteralActivityLossConstantsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact
  using (baseBelowBasePlusRemainder)
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Product

------------------------------------------------------------------------
-- Literature normalization.
--
-- B. C. Hall, "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3
--
-- S. Helgason, "Differential Geometry, Lie Groups, and Symmetric Spaces",
-- American Mathematical Society (2001). DOI: 10.1090/gsm/034
--
-- T. D. Barfoot, "State Estimation for Robotics", Cambridge University
-- Press (2017). DOI: 10.1017/9781316671528
--
-- B. Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
--
-- T. Balaban, "Ultraviolet Stability of Three-Dimensional Lattice Pure Gauge
-- Field Theories", Communications in Mathematical Physics 102 (1985),
-- 255--275. DOI: 10.1007/BF01229381
--
-- E. B. Dynkin, "Calculation of the coefficients in the Campbell-Hausdorff
-- formula", Doklady Akademii Nauk SSSR 57 (1947), 323--326. No DOI assigned.
--
-- The SU(2) Haar density convention is
--
--   j(A) = (sin(|A|/2)/(|A|/2))^2.
--
-- The plaquette remainder lane below permits the exact quaternion-product route;
-- it does not force a generic infinite BCH-series estimate.
------------------------------------------------------------------------

quarter half oneSixteenth : ℚ
quarter = + 1 / 4
half = + 1 / 2
oneSixteenth = + 1 / 16

quarterBelowHalf : quarter ≤ half
quarterBelowHalf =
  subst
    (λ upper → quarter ≤ upper)
    (ℚRing.solve-∀ {x = quarter + quarter})
    (baseBelowBasePlusRemainder quarter quarter
      (let instance _ = ℚP.normalize-nonNeg 1 4 in ℚP.nonNegative⁻¹ quarter))

------------------------------------------------------------------------
-- Haar density in the exponential chart.
------------------------------------------------------------------------

record SU2HaarLossData
    (Link Polymer Scalar : Set) : Set₁ where
  field
    zero one two : Scalar
    add multiply divide square exp log sine abs : Scalar → Scalar → Scalar
    norm radius : Link → Scalar
    polymerLinks : Polymer → List Link
    polymerSize : Polymer → Nat

    sinOverX : Scalar → Scalar
    haarDensity : Link → Scalar
    haarJacobianProduct : Polymer → Scalar
    haarLogLoss : Polymer → Scalar

    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    InChart : Link → Set

    su2HaarDensityExponentialCoordinatesExact : ∀ link →
      InChart link →
      haarDensity link
      ≡ square (sinOverX (divide (norm link) two)) one

    su2HaarLogDensityExact : ∀ link →
      InChart link →
      log (haarDensity link) one
      ≡ multiply two
          (log (sinOverX (divide (norm link) two)) one)

    sinOverXLowerBoundOnChart : ∀ link →
      InChart link →
      LessEqual (lowerSinc link) (sinOverX (divide (norm link) two))
    lowerSinc : Link → Scalar

    negativeLogSinOverXQuadraticBound : ∀ link →
      InChart link →
      LessEqual
        (negativeLogSinc link)
        (multiply (haarQuadraticConstant link)
          (square (norm link) one))
    negativeLogSinc haarQuadraticConstant : Link → Scalar

    haarLogDensityQuadraticBound : ∀ link →
      InChart link →
      LessEqual (singleLinkHaarLoss link)
        (multiply (singleLinkLossConstant link)
          (square (norm link) one))
    singleLinkHaarLoss singleLinkLossConstant : Link → Scalar

    haarJacobianProductOverBondsExact : ∀ polymer → Set

    allPolymerLinksInChart : ∀ polymer link → Set
    linkNormBelowRadius : ∀ polymer link → Set

    polymerLossPerBlock : Scalar
    haarJacobianPolymerLossBound : ∀ polymer →
      LessEqual (haarLogLoss polymer)
        (natScale polymerLossPerBlock (polymerSize polymer))

    natScale : Scalar → Nat → Scalar

open SU2HaarLossData public

------------------------------------------------------------------------
-- Relative determinant and trace-log localization.
------------------------------------------------------------------------

record RelativeDeterminantLossData
    (Index Polymer Operator Scalar : Set) : Set₁ where
  field
    referenceHessian physicalHessian relativeHessian : Index → Operator
    operatorNorm traceNorm : Operator → Scalar
    identityOperator : Operator
    addOperator composeOperator : Operator → Operator → Operator
    inverseSquareRoot : Operator → Operator

    determinantFactor : Index → Polymer → Scalar
    logDetRelative : Index → Polymer → Scalar
    traceLogSeries : Operator → Scalar

    zero one half : Scalar
    add multiply divide : Scalar → Scalar → Scalar
    LessEqual StrictLess : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    SmallFieldIndex : Index → Set

    physicalFluctuationHessianRelativeFactorization : ∀ index →
      SmallFieldIndex index →
      physicalHessian index
      ≡ composeOperator (inverseSquareRoot (referenceHessian index))
          (composeOperator
            (addOperator identityOperator (relativeHessian index))
            (inverseSquareRoot (referenceHessian index)))

    relativeHessianOperatorDefinition : ∀ index →
      relativeHessian index
      ≡ composeOperator (inverseSquareRoot (referenceHessian index))
          (composeOperator
            (hessianDifference index)
            (inverseSquareRoot (referenceHessian index)))
    hessianDifference : Index → Operator

    relativeHessianNormBoundFromFormBound : ∀ index →
      SmallFieldIndex index →
      LessEqual (operatorNorm (relativeHessian index)) (relativeRadius index)
    relativeRadius : Index → Scalar

    relativeRadiusBelowHalf : ∀ index →
      SmallFieldIndex index → LessEqual (relativeRadius index) half

    logDetRelativeHessianExact : ∀ index polymer →
      SmallFieldIndex index →
      logDetRelative index polymer
      ≡ localizedTraceLog index polymer
    localizedTraceLog : Index → Polymer → Scalar

    traceLogSeriesExact : ∀ index →
      SmallFieldIndex index →
      traceLogSeries (relativeHessian index)
      ≡ exactTraceLog index
    exactTraceLog : Index → Scalar

    traceLogSeriesAbsoluteBound : ∀ index →
      SmallFieldIndex index →
      LessEqual (absoluteTraceLog index)
        (divide (traceNorm (relativeHessian index))
          (subtractOne (operatorNorm (relativeHessian index))))
    absoluteTraceLog subtractOne : Scalar → Scalar

    finiteRangeTraceLocalization : ∀ index polymer → Set
    determinantPolymerConnectedDecomposition : ∀ index polymer → Set

    traceNormPerPolymerBlockBound : ∀ index polymer →
      SmallFieldIndex index →
      LessEqual (localizedTraceNorm index polymer)
        (natScale (determinantLossPerBlock index) (polymerSize polymer))
    localizedTraceNorm : Index → Polymer → Scalar
    determinantLossPerBlock : Index → Scalar
    polymerSize : Polymer → Nat
    natScale : Scalar → Nat → Scalar

    fluctuationDeterminantPolymerLossBound : ∀ index polymer →
      SmallFieldIndex index →
      LessEqual (determinantLogLoss index polymer)
        (natScale (determinantLossPerBlock index) (polymerSize polymer))
    determinantLogLoss : Index → Polymer → Scalar

open RelativeDeterminantLossData public

relativeHessianNormBelowHalf :
  ∀ {Index Polymer Operator Scalar}
    (dataSet : RelativeDeterminantLossData Index Polymer Operator Scalar)
    index → SmallFieldIndex dataSet index →
  LessEqual dataSet (operatorNorm dataSet (relativeHessian dataSet index))
    (half dataSet)
relativeHessianNormBelowHalf dataSet index small =
  transitive dataSet
    (relativeHessianNormBoundFromFormBound dataSet index small)
    (relativeRadiusBelowHalf dataSet index small)

------------------------------------------------------------------------
-- Exact quaternion plaquette product and cubic remainder.
------------------------------------------------------------------------

record SU2QuaternionPlaquetteBCHData
    (Link Lie Quaternion Scalar Polymer : Set) : Set₁ where
  field
    exponential inverse multiplyQuaternion : Link → Quaternion
    multiplyQ : Quaternion → Quaternion → Quaternion
    logarithm : Quaternion → Lie
    linearCurl quadraticCommutator cubicRemainder :
      Link → Link → Link → Link → Lie
    addLie : Lie → Lie → Lie
    normLie : Lie → Scalar
    linkRadius : Link → Scalar

    fourLinkHolonomy : Link → Link → Link → Link → Quaternion
    fourLinkHolonomyDefinition : ∀ a b c d →
      fourLinkHolonomy a b c d
      ≡ multiplyQ (exponential a)
          (multiplyQ (exponential b)
            (multiplyQ (inverse c) (inverse d)))

    fourLinkPlaquetteBCHSecondOrderExact : ∀ a b c d →
      logarithm (fourLinkHolonomy a b c d)
      ≡ addLie (linearCurl a b c d)
          (addLie (quadraticCommutator a b c d)
            (cubicRemainder a b c d))

    fourLinkPlaquetteBCHThirdOrderRemainder : ∀ a b c d → Set

    LessEqual : Scalar → Scalar → Set
    plaquetteBCHRemainderCubicBound : ∀ a b c d →
      LinksInChart a b c d →
      LessEqual (normLie (cubicRemainder a b c d))
        (cubicMajorant a b c d)
    LinksInChart : Link → Link → Link → Link → Set
    cubicMajorant : Link → Link → Link → Link → Scalar

    polymerPlaquettes : Polymer → List (Link ×4 Link)
    polymerSize : Polymer → Nat
    bchLossPerBlock : Scalar
    polymerBCHRemainderSumBound : ∀ polymer →
      LessEqual (polymerBCHLoss polymer)
        (natScale bchLossPerBlock (polymerSize polymer))
    bchActionExponentialLossBound : ∀ polymer →
      LessEqual (bchExponentialFactor polymer)
        (exponentialOfNatScale bchLossPerBlock (polymerSize polymer))

    polymerBCHLoss bchExponentialFactor : Polymer → Scalar
    natScale : Scalar → Nat → Scalar
    exponentialOfNatScale : Scalar → Nat → Scalar

    _×4_ : Set → Set → Set

open SU2QuaternionPlaquetteBCHData public

------------------------------------------------------------------------
-- Local Taylor projection and patch transfer.
------------------------------------------------------------------------

record LocalizationLossData
    (Scale Polymer Activity Scalar : Set) : Set₁ where
  field
    localization TaylorProjector remainder : Scale → Activity → Activity
    norm : Scale → Polymer → Activity → Scalar
    supportCollar : Polymer → Polymer
    collarWidth : Polymer → Nat
    blockingFactor dimensionGain decayRate localizationConstant : Scalar
    multiply exp : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    localizationTaylorProjectorExact : ∀ scale activity →
      localization scale activity ≡ TaylorProjector scale activity
    localizationRemainderIntegralFormula : ∀ scale activity → Set
    localizationDerivativeOrderGain : ∀ scale polymer activity → Set
    localizationSupportCollarExact : ∀ scale polymer activity → Set
    localizationCollarCountingBound : ∀ polymer → Set
    localizationExponentialWeightGain : ∀ scale polymer activity → Set

    localizationPolymerLossBound : ∀ scale polymer activity →
      LessEqual (norm (sucScale scale) polymer (remainder scale activity))
        (multiply localizationConstant
          (multiply (blockingGain scale)
            (multiply (collarGain polymer)
              (norm scale polymer activity))))

    sucScale : Scale → Scale
    blockingGain : Scale → Scalar
    collarGain : Polymer → Scalar

open LocalizationLossData public

record PatchActivityLossData
    (Regime Polymer Activity Scalar : Set) : Set₁ where
  field
    boundary interface corner nested : Regime
    extend restrict : Regime → Activity → Activity
    norm : Regime → Polymer → Activity → Scalar
    patchConstant : Regime → Scalar
    weightLoss : Regime → Polymer → Scalar
    multiply : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    boundaryActivityExtensionExact : ∀ activity → Set
    interfaceActivityExtensionExact : ∀ activity → Set
    cornerActivityExtensionExact : ∀ activity → Set
    nestedActivityExtensionExact : ∀ activity → Set

    boundaryPatchNormComparison : ∀ polymer activity →
      LessEqual (norm boundary polymer (extend boundary activity))
        (multiply (patchConstant boundary) (norm boundary polymer activity))
    interfacePatchNormComparison : ∀ polymer activity →
      LessEqual (norm interface polymer (extend interface activity))
        (multiply (patchConstant interface) (norm interface polymer activity))
    cornerPatchNormComparison : ∀ polymer activity →
      LessEqual (norm corner polymer (extend corner activity))
        (multiply (patchConstant corner) (norm corner polymer activity))
    nestedPatchNormComparison : ∀ polymer activity →
      LessEqual (norm nested polymer (extend nested activity))
        (multiply (patchConstant nested) (norm nested polymer activity))

    transferCutCollarExcessBound : ∀ regime polymer → Set
    transferCutActivityPenalty : ∀ regime polymer activity → Set
    nestedLocalizationCommutesWithRestriction : ∀ polymer activity → Set

    commonPatchLoss : Scalar
    patchLossUniformAcrossRegimes : ∀ regime polymer activity →
      LessEqual (norm regime polymer (extend regime activity))
        (multiply commonPatchLoss (norm regime polymer activity))

open PatchActivityLossData public

------------------------------------------------------------------------
-- One gain-minus-loss ledger.  This is the endpoint consumed by the six-factor
-- product module; the five losses are allowed to exceed one individually.
------------------------------------------------------------------------

record LiteralActivityNetGainData
    (Scale Polymer Scalar : Set) : Set₁ where
  field
    actionGain jacobianLoss determinantLoss bchLoss localizationLoss patchLoss :
      Scale → Polymer → Scalar
    totalLoss netGain logSixteen : Scale → Polymer → Scalar
    activity factorProduct oneSixteenth : Scale → Polymer → Scalar

    add subtract : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    totalLossDefinition : ∀ scale polymer →
      totalLoss scale polymer
      ≡ add (jacobianLoss scale polymer)
          (add (determinantLoss scale polymer)
            (add (bchLoss scale polymer)
              (add (localizationLoss scale polymer)
                (patchLoss scale polymer))))

    netGainDefinition : ∀ scale polymer →
      netGain scale polymer
      ≡ subtract (actionGain scale polymer) (totalLoss scale polymer)

    literalWilsonActivityLogBound : ∀ scale polymer →
      LessEqual (activity scale polymer) (factorProduct scale polymer)

    physicalNetGainAtLeastLogSixteen : ∀ scale polymer →
      LessEqual (logSixteen scale polymer) (netGain scale polymer)

    logGainImpliesFactorProductBelow : ∀ scale polymer →
      LessEqual (logSixteen scale polymer) (netGain scale polymer) →
      LessEqual (factorProduct scale polymer) (oneSixteenth scale polymer)

open LiteralActivityNetGainData public

physicalFactorProductBelowOneSixteenth :
  ∀ {Scale Polymer Scalar}
    (dataSet : LiteralActivityNetGainData Scale Polymer Scalar)
    scale polymer →
  LessEqual dataSet (factorProduct dataSet scale polymer)
    (oneSixteenth dataSet scale polymer)
physicalFactorProductBelowOneSixteenth dataSet scale polymer =
  logGainImpliesFactorProductBelow dataSet scale polymer
    (physicalNetGainAtLeastLogSixteen dataSet scale polymer)

literalWilsonActivityPerTraversalBelowOneSixteenth :
  ∀ {Scale Polymer Scalar}
    (dataSet : LiteralActivityNetGainData Scale Polymer Scalar)
    scale polymer →
  LessEqual dataSet (activity dataSet scale polymer)
    (oneSixteenth dataSet scale polymer)
literalWilsonActivityPerTraversalBelowOneSixteenth dataSet scale polymer =
  transitive dataSet
    (literalWilsonActivityLogBound dataSet scale polymer)
    (physicalFactorProductBelowOneSixteenth dataSet scale polymer)

su2HaarDensityFormulaLevel : ProofLevel
su2HaarDensityFormulaLevel = machineChecked

relativeDeterminantReductionLevel : ProofLevel
relativeDeterminantReductionLevel = machineChecked

quaternionPlaquetteBCHReductionLevel : ProofLevel
quaternionPlaquetteBCHReductionLevel = machineChecked

localizationPatchLossReductionLevel : ProofLevel
localizationPatchLossReductionLevel = machineChecked

literalNetGainClosureLevel : ProofLevel
literalNetGainClosureLevel = machineChecked

haarTranscendentalIntervalInputsLevel : ProofLevel
haarTranscendentalIntervalInputsLevel = conditional

physicalTraceLogLocalizationInputsLevel : ProofLevel
physicalTraceLogLocalizationInputsLevel = conditional

physicalQuaternionCubicRemainderInputsLevel : ProofLevel
physicalQuaternionCubicRemainderInputsLevel = conditional

physicalLocalizationPatchNormInputsLevel : ProofLevel
physicalLocalizationPatchNormInputsLevel = conditional

physicalLogSixteenWitnessLevel : ProofLevel
physicalLogSixteenWitnessLevel = conditional
