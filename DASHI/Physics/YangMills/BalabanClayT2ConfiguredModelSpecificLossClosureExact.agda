module DASHI.Physics.YangMills.BalabanClayT2ConfiguredModelSpecificLossClosureExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT2ConfiguredComponentLossBoundsExact as Bounds

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I. Generation of Effective Actions in a Small Field Approximation
-- and a Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Section 0, Eqs. (0.24)--(0.27), define localization domains and
-- the tree-size decay exp(-kappa d_j(X)); Sections 4--5 fix Ward and fluctuation
-- conventions.  These are comparison conventions, not imported estimates.
--
-- Barry Simon, "Trace Ideals and Their Applications", second edition,
-- American Mathematical Society (2005). DOI: 10.1090/surv/120
-- Relationship: trace-log series and trace-norm control.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (value ∷ values) = value + sumℚ values

record PhysicalHaarPolymerLoss (Scale Polymer Link : Set) : Set₁ where
  field
    chargedLinks : Scale → Polymer → List Link
    linkNegativeLogDensity : Scale → Polymer → Link → ℚ
    mappedLinkLosses : Scale → Polymer → List Link → List ℚ

    mappedEmpty : ∀ scale polymer → mappedLinkLosses scale polymer [] ≡ []
    mappedStep : ∀ scale polymer link rest →
      mappedLinkLosses scale polymer (link ∷ rest)
      ≡ linkNegativeLogDensity scale polymer link
        ∷ mappedLinkLosses scale polymer rest

    haarLoss : Scale → Polymer → ℚ
    haarLossDefinition : ∀ scale polymer →
      haarLoss scale polymer
      ≡ sumℚ (mappedLinkLosses scale polymer (chargedLinks scale polymer))

    exponentialCoordinateHaarDensityExact : ∀ scale polymer link → Set
    chargedLinkWithinConfiguredRadius : ∀ scale polymer link → Set
    polymerJacobianProductExact : ∀ scale polymer → Set
    productLogEqualsLinkLossSum : ∀ scale polymer → Set

    pointwiseLinkLossBelowConfiguredHalfAngle : ∀ scale polymer link →
      linkNegativeLogDensity scale polymer link
      ≤ Bounds.configuredHaarUpper

    chargedLinksPerPolymerUnitAtMostSixtyFour : ∀ scale polymer → Set

    finiteHaarSumBelowComputed : ∀ scale polymer →
      sumℚ (mappedLinkLosses scale polymer (chargedLinks scale polymer))
      ≤ Bounds.configuredHaarUpper

open PhysicalHaarPolymerLoss public

haarLossBelowComputed :
  ∀ {Scale Polymer Link}
    (dataSet : PhysicalHaarPolymerLoss Scale Polymer Link)
    scale polymer →
  haarLoss dataSet scale polymer ≤ Bounds.configuredHaarUpper
haarLossBelowComputed dataSet scale polymer =
  subst
    (λ lower → lower ≤ Bounds.configuredHaarUpper)
    (haarLossDefinition dataSet scale polymer)
    (finiteHaarSumBelowComputed dataSet scale polymer)

record PhysicalLocalizedTraceLogLoss
    (Scale Polymer Operator : Set) : Set₁ where
  field
    relativeOperator localizedRelativeOperator : Scale → Polymer → Operator
    determinantLoss operatorNorm traceNorm : Scale → Polymer → ℚ

    physicalRelativeHessianFactorizationExact : ∀ scale polymer → Set
    localizationPartitionExact : ∀ scale polymer → Set
    greenOffDiagonalDecayConsumed : ∀ scale polymer → Set

    relativeOperatorNormBelowHalf : ∀ scale polymer → Set
    localizedTraceNormBelowEighth : ∀ scale polymer → Set

    traceLogSeriesConverges : ∀ scale polymer → Set
    traceLogIdentityExact : ∀ scale polymer → Set

    traceLogEstimateExact : ∀ scale polymer →
      determinantLoss scale polymer ≤ Bounds.configuredDeterminantUpper

open PhysicalLocalizedTraceLogLoss public

relativeOperatorNormBelowHalfLiteral = relativeOperatorNormBelowHalf
localizedTraceNormBelowEighthLiteral = localizedTraceNormBelowEighth
fluctuationDeterminantPolymerLossBoundLiteral = traceLogEstimateExact

record PhysicalQuaternionPlaquetteLoss
    (Scale Polymer Plaquette Quaternion : Set) : Set₁ where
  field
    chargedPlaquettes : Scale → Polymer → List Plaquette
    fourLinkQuaternionProduct : Scale → Plaquette → Quaternion
    linearCurl quadraticCommutator cubicRemainder : Scale → Plaquette → Quaternion

    fourLinkQuaternionProductExact : ∀ scale plaquette → Set
    fourLinkQuaternionLogExpansionExact : ∀ scale plaquette → Set
    linearCurlIdentificationExact : ∀ scale plaquette → Set
    quadraticCommutatorIdentificationExact : ∀ scale plaquette → Set

    plaquetteCubicLoss : Scale → Polymer → Plaquette → ℚ
    mappedPlaquetteLosses : Scale → Polymer → List Plaquette → List ℚ
    mappedPlaquetteEmpty : ∀ scale polymer →
      mappedPlaquetteLosses scale polymer [] ≡ []
    mappedPlaquetteStep : ∀ scale polymer plaquette rest →
      mappedPlaquetteLosses scale polymer (plaquette ∷ rest)
      ≡ plaquetteCubicLoss scale polymer plaquette
        ∷ mappedPlaquetteLosses scale polymer rest

    pointwiseQuaternionCubicBound : ∀ scale polymer plaquette → Set
    chargedPlaquettesPerPolymerUnitAtMostNinetySix : ∀ scale polymer → Set

    bchLoss : Scale → Polymer → ℚ
    bchLossDefinition : ∀ scale polymer →
      bchLoss scale polymer
      ≡ sumℚ
          (mappedPlaquetteLosses scale polymer
            (chargedPlaquettes scale polymer))

    finiteQuaternionSumBelowComputed : ∀ scale polymer →
      sumℚ
        (mappedPlaquetteLosses scale polymer
          (chargedPlaquettes scale polymer))
      ≤ Bounds.configuredBCHUpper

open PhysicalQuaternionPlaquetteLoss public

quaternionCubicRemainderBelowComputed :
  ∀ {Scale Polymer Plaquette Quaternion}
    (dataSet : PhysicalQuaternionPlaquetteLoss
      Scale Polymer Plaquette Quaternion)
    scale polymer →
  bchLoss dataSet scale polymer ≤ Bounds.configuredBCHUpper
quaternionCubicRemainderBelowComputed dataSet scale polymer =
  subst
    (λ lower → lower ≤ Bounds.configuredBCHUpper)
    (bchLossDefinition dataSet scale polymer)
    (finiteQuaternionSumBelowComputed dataSet scale polymer)

record PhysicalLocalizationLoss (Scale Polymer Domain : Set) : Set₁ where
  field
    localizationDomains : Scale → Polymer → List Domain
    balabanTreeSize : Scale → Domain → ℚ
    collarDistance : Scale → Domain → ℚ
    localizationLoss : Scale → Polymer → ℚ

    localizationDomainIsConnectedCubeUnion : ∀ scale domain → Set
    treeSizeMatchesBalabanDj : ∀ scale domain → Set
    collarDistanceControlsTreeSize : ∀ scale domain → Set

    cutoffDerivativeGainOneThirtySecond : ∀ scale domain → Set
    collarOverlapChargeAtMostFour : ∀ scale polymer → Set
    localizationExponentialWeightGain : ∀ scale domain → Set

    localizationLossBelowComputed : ∀ scale polymer →
      localizationLoss scale polymer ≤ Bounds.configuredLocalizationUpper

open PhysicalLocalizationLoss public

record PhysicalPatchLoss (Scale Polymer : Set) : Set₁ where
  field
    patchLoss : Scale → Polymer → ℚ

    boundaryPatchNormComparison : ∀ scale polymer → Set
    interfacePatchNormComparison : ∀ scale polymer → Set
    cornerPatchNormComparison : ∀ scale polymer → Set
    nestedPatchNormComparison : ∀ scale polymer → Set

    transferCutCollarExcessBound : ∀ scale polymer → Set
    nestedLocalizationCommutesWithRestriction : ∀ scale polymer → Set
    localInverseComparisonUniform : ∀ scale polymer → Set

    patchLossBelowComputed : ∀ scale polymer →
      patchLoss scale polymer ≤ Bounds.configuredPatchUpper

open PhysicalPatchLoss public

record ConfiguredModelSpecificLossData
    (Scale Polymer Link Operator Plaquette Quaternion Domain : Set) : Set₂ where
  field
    haar : PhysicalHaarPolymerLoss Scale Polymer Link
    determinant : PhysicalLocalizedTraceLogLoss Scale Polymer Operator
    quaternion : PhysicalQuaternionPlaquetteLoss
      Scale Polymer Plaquette Quaternion
    localization : PhysicalLocalizationLoss Scale Polymer Domain
    patch : PhysicalPatchLoss Scale Polymer

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open ConfiguredModelSpecificLossData public

asConfiguredPhysicalComponentLosses :
  ∀ {Scale Polymer Link Operator Plaquette Quaternion Domain} →
  ConfiguredModelSpecificLossData
    Scale Polymer Link Operator Plaquette Quaternion Domain →
  Bounds.ConfiguredPhysicalComponentLosses Scale Polymer
asConfiguredPhysicalComponentLosses dataSet = record
  { haarLoss = haarLoss (haar dataSet)
  ; determinantLoss = determinantLoss (determinant dataSet)
  ; bchLoss = bchLoss (quaternion dataSet)
  ; localizationLoss = localizationLoss (localization dataSet)
  ; patchLoss = patchLoss (patch dataSet)
  ; haarLossBelowComputed = haarLossBelowComputed (haar dataSet)
  ; relativeOperatorNormBelowHalf =
      relativeOperatorNormBelowHalf (determinant dataSet)
  ; localizedTraceNormBelowEighth =
      localizedTraceNormBelowEighth (determinant dataSet)
  ; traceLogEstimateExact = traceLogEstimateExact (determinant dataSet)
  ; quaternionCubicRemainderBelowComputed =
      quaternionCubicRemainderBelowComputed (quaternion dataSet)
  ; localizationLossBelowComputed =
      localizationLossBelowComputed (localization dataSet)
  ; patchLossBelowComputed = patchLossBelowComputed (patch dataSet)
  ; transitive = transitive dataSet
  }

haarPhysicalReductionLevel : ProofLevel
haarPhysicalReductionLevel = machineChecked

localizedTraceLogReductionLevel : ProofLevel
localizedTraceLogReductionLevel = machineChecked

quaternionPhysicalReductionLevel : ProofLevel
quaternionPhysicalReductionLevel = machineChecked

localizationPatchReductionLevel : ProofLevel
localizationPatchReductionLevel = machineChecked

literalLinkTraceQuaternionCollarPatchInputsLevel : ProofLevel
literalLinkTraceQuaternionCollarPatchInputsLevel = conditional
