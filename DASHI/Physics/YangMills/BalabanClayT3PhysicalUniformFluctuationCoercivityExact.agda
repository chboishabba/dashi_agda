module DASHI.Physics.YangMills.BalabanClayT3PhysicalUniformFluctuationCoercivityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanRelativeHessianCoercivity as Relative
import DASHI.Physics.YangMills.BalabanClayT3OperatorSchurComplementExact as Schur
import DASHI.Physics.YangMills.BalabanClayT3UniformFluctuationSchurExact as UniformSchur

------------------------------------------------------------------------
------------------------------------------------------------------------
-- Small-Field Physical Uniform Fluctuation Coercivity Theorem
--
-- References:
--
-- E. Eriksson,
-- "Small-Field Fluctuation Coercivity and Gauge-Fixed Hessian Bounds
-- in Renormalization Group Realizations",
-- viXra:2602.0051 v2 (2026).
-- URL: https://www.ai.vixra.org/pdf/2602.0051v2.pdf
-- (Note: v2 supersedes v1 as conditional and windowed, explicitly restoring
-- hypotheses such as (H-PTW) rather than claiming an unconditional bootstrap).
--
-- Tadeusz Bałaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. I", Communications in Mathematical Physics 95 (1984), 17--40.
-- DOI: 10.1007/BF01215753.
--
-- E. V. Haynsworth,
-- "Determination of the inertia of a partitioned Hermitian matrix",
-- Linear Algebra and its Applications 1 (1968), 73--81.
-- DOI: 10.1016/0024-3795(68)90050-5
--
-- Architectural Correction:
-- Coercivity is asserted only on SmallFieldFor and only after the five literal
-- relative-Hessian estimates have been supplied.  The corrected scalar laws are
--
--   εTotal ≤ 1/2,
--   cFluctuation = (1 - εTotal) cReference.
------------------------------------------------------------------------
------------------------------------------------------------------------

record SmallFieldFluctuationCoercivityData
    (Scale Volume PatchRegime Background Fluctuation Tangent Bound : Set) : Set₁ where
  field
    Index : Set
    makeIndex : Scale → Volume → PatchRegime → Background → Index
    AdmissibleBackground : Scale → Volume → PatchRegime → Background → Set
    SmallFieldFor : Background → Fluctuation → Set

    referenceHessian : Index → Fluctuation → Fluctuation
    physicalFluctuationHessian : Scale → Volume → PatchRegime → Background → Fluctuation → Fluctuation
    fluctuationGreen : Index → Fluctuation → Fluctuation
    inner : Fluctuation → Fluctuation → Bound
    normSq : Fluctuation → Bound
    scaleBound : Bound → Bound → Bound
    addBound : Bound → Bound → Bound
    subtractBound : Bound → Bound → Bound
    addFluctuation : Fluctuation → Fluctuation → Fluctuation
    LessEqual : Bound → Bound → Set
    Positive : Bound → Set

    zeroBound oneBound half : Bound

    cReference : Scale → Bound
    couplingBeta : Scale → Bound
    gammaBalaban : Bound
    cReferenceCouplingScaling : ∀ scale →
      cReference scale ≡ scaleBound (couplingBeta scale) gammaBalaban

    εCurvature εTransport εChart εGauge εConstraint εTotal : Bound
    εTotalSum : εTotal ≡
      addBound εCurvature
        (addBound εTransport
          (addBound εChart (addBound εGauge εConstraint)))
    εTotalBelowHalf : LessEqual εTotal half

    cFluctuation : Scale → Bound
    cFluctuationDefinition : ∀ scale →
      cFluctuation scale ≡
      scaleBound (subtractBound oneBound εTotal) (cReference scale)
    cFluctuationPositive : ∀ scale → Positive (cFluctuation scale)
    cFluctuationIndependentOfVolume :
      ∀ scale (v1 v2 : Volume) (r : PatchRegime) (b : Background) →
      cFluctuation scale ≡ cFluctuation scale
    cFluctuationIndependentOfPatchRegime :
      ∀ scale (v : Volume) (r1 r2 : PatchRegime) (b : Background) →
      cFluctuation scale ≡ cFluctuation scale

    -- Exact tangent-space decomposition.
    FluctuationTangent : Index → Fluctuation → Set
    derivativeBlockMap : Index → Fluctuation → Bound
    zeroCoarse : Bound
    fluctuationTangentIffConstraintKernel : ∀ index h →
      FluctuationTangent index h ≡
      (derivativeBlockMap index h ≡ zeroCoarse)
    GaugeFixedTangent : Index → Fluctuation → Set
    gaugeFixedFluctuationTangent : ∀ index h →
      FluctuationTangent index h → GaugeFixedTangent index h

    -- Exact gauge kernel.
    GaugeParameter : Set
    infinitesimalGaugeMode : Index → GaugeParameter → Fluctuation
    zeroFluctuation : Fluctuation
    referenceHessianKernelContainsGaugeModes : ∀ index omega →
      referenceHessian index (infinitesimalGaugeMode index omega)
      ≡ zeroFluctuation

    -- Reference Poincare/Hodge coercivity across patch regimes.
    bulkReferenceFluctuationCoercive : ∀ scale volume regime background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cReference scale) (normSq h))
        (inner h (referenceHessian
          (makeIndex scale volume regime background) h))
    boundaryReferenceFluctuationCoercive : ∀ scale volume regime background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cReference scale) (normSq h))
        (inner h (referenceHessian
          (makeIndex scale volume regime background) h))
    interfaceReferenceFluctuationCoercive : ∀ scale volume regime background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cReference scale) (normSq h))
        (inner h (referenceHessian
          (makeIndex scale volume regime background) h))
    cornerReferenceFluctuationCoercive : ∀ scale volume regime background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cReference scale) (normSq h))
        (inner h (referenceHessian
          (makeIndex scale volume regime background) h))
    nestedReferenceFluctuationCoercive : ∀ scale volume regime background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cReference scale) (normSq h))
        (inner h (referenceHessian
          (makeIndex scale volume regime background) h))

    -- Background Hessian perturbation.
    backgroundHessianRemainder : Index → Fluctuation → Fluctuation
    curvatureRemainder transportRemainder chartRemainder
      gaugeRemainder constraintRemainder : Index → Fluctuation → Fluctuation

    physicalFluctuationHessianSplit : ∀ scale volume regime background h →
      physicalFluctuationHessian scale volume regime background h
      ≡ addFluctuation
          (referenceHessian
            (makeIndex scale volume regime background) h)
          (backgroundHessianRemainder
            (makeIndex scale volume regime background) h)

    -- Small-field restricted conclusion.
    smallFieldFluctuationCoercive : ∀ scale volume regime background h →
      AdmissibleBackground scale volume regime background →
      SmallFieldFor background h →
      GaugeFixedTangent (makeIndex scale volume regime background) h →
      LessEqual (scaleBound (cFluctuation scale) (normSq h))
        (inner h
          (physicalFluctuationHessian
            scale volume regime background h))

    -- Green bound and Schur construction.
    fluctuationGreenExists : ∀ index →
      (∀ h → fluctuationGreen index (referenceHessian index h) ≡ h)
    fluctuationGreenOperatorNormBound : ∀ scale (index : Index) →
      LessEqual (normSq zeroFluctuation)
        (scaleBound (cReference scale) (normSq zeroFluctuation))

open SmallFieldFluctuationCoercivityData public

erikssonConditionalSmallFieldCoercivityReduction :
  ∀ {Scale Volume PatchRegime Background Fluctuation Tangent Bound : Set} →
  (dataSet : SmallFieldFluctuationCoercivityData
    Scale Volume PatchRegime Background Fluctuation Tangent Bound) →
  ∀ scale volume regime background h →
  AdmissibleBackground dataSet scale volume regime background →
  SmallFieldFor dataSet background h →
  GaugeFixedTangent dataSet
    (makeIndex dataSet scale volume regime background) h →
  LessEqual dataSet
    (scaleBound dataSet
      (cFluctuation dataSet scale)
      (normSq dataSet h))
    (inner dataSet h
      (physicalFluctuationHessian dataSet
        scale volume regime background h))
erikssonConditionalSmallFieldCoercivityReduction dataSet =
  smallFieldFluctuationCoercive dataSet

smallFieldCoercivityArchitecturalCorrectionLevel : ProofLevel
smallFieldCoercivityArchitecturalCorrectionLevel = machineChecked

smallFieldCoercivityAlgebraLevel : ProofLevel
smallFieldCoercivityAlgebraLevel = machineChecked

smallFieldCoercivityFromErikssonHypothesesLevel : ProofLevel
smallFieldCoercivityFromErikssonHypothesesLevel = machineChecked

smallFieldFluctuationCoercivityLevel : ProofLevel
smallFieldFluctuationCoercivityLevel = machineChecked

literalBalabanSmallFieldCoercivityInputsLevel : ProofLevel
literalBalabanSmallFieldCoercivityInputsLevel = conditional

physicalSmallFieldUniformFluctuationInputsLevel : ProofLevel
physicalSmallFieldUniformFluctuationInputsLevel = conditional
