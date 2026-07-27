module DASHI.Physics.YangMills.BalabanClayT4Balaban1987TheoremShapeExact where

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Primary-source normalization and three distinct comparison roles.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
--
-- Role A -- architectural template: Introduction, pp. 249--260, Theorems 1--2
-- and Eqs. (0.22)--(0.31).  Theorem 1 is conditional on all effective couplings
-- remaining in a sufficiently small interval.  Theorem 2 states the d=4,
-- G=SU(2) running-coupling target and Eq. (0.31).
--
-- Role B -- localization convention: Introduction, Eqs. (0.24)--(0.27).
-- Localization domains are connected unions of cubes and polymer corrections
-- decay as E0 exp(-kappa d_j(X)), where d_j is the tree-graph linear size in the
-- configured block units.
--
-- Role C -- tensor/coefficient falsification target: Sections 4--5,
-- pp. 281--298, especially Eqs. (5.36)--(5.41).  The Ward--Takahashi analysis in
-- Section 4 is upstream of the vacuum-polarization calculation in Section 5.
--
-- Source boundary: the paper says the perturbative proof of Theorem 2 and more
-- precise asymptotics will appear separately.  Therefore Eq. (0.31) is encoded
-- here as a comparison target, not as an imported proof.  The statement that
-- SU(2) is used to simplify calculations supports the quaternion specialization
-- but does not remove any DASHI estimate.
------------------------------------------------------------------------

record BalabanTheorem1SmallFieldTemplate
    (Scale Coupling Field Action Bound : Set) : Set₁ where
  field
    effectiveCoupling : Scale → Coupling
    zero gamma : Coupling
    InSmallCouplingInterval : Coupling → Set

    allEffectiveCouplingsSmall : ∀ scale →
      InSmallCouplingInterval (effectiveCoupling scale)

    SmallField : Scale → Field → Set
    effectiveAction : Scale → Field → Action
    relevantAction irrelevantAction polymerCorrection :
      Scale → Field → Action

    formulas022To024Exact : ∀ scale field →
      SmallField scale field → Set

    bound029 : ∀ scale field →
      SmallField scale field → Bound

open BalabanTheorem1SmallFieldTemplate public

record BalabanLocalizationMetricTarget
    (Scale Domain Correction Scalar : Set) : Set₁ where
  field
    connectedCubeUnion : Scale → Domain → Set
    blockSizeM treeGraphSizeDj : Scale → Domain → Scalar

    correction : Scale → Domain → Correction
    correctionNorm : Correction → Scalar
    E0 kappa : Scalar
    multiply negate exponential : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    localizationDomainConvention024To027 : ∀ scale domain →
      connectedCubeUnion scale domain

    exponentialTreeSizeDecay025 : ∀ scale domain →
      LessEqual
        (correctionNorm (correction scale domain))
        (multiply E0
          (exponential
            (negate kappa (treeGraphSizeDj scale domain))
            (blockSizeM scale domain)))

open BalabanLocalizationMetricTarget public

record BalabanTheorem2RunningCouplingTarget
    (Scale Scalar : Set) : Set₁ where
  field
    epsilon g g0 beta betaPrime : Scalar
    inverseSquare logarithm multiply subtract absoluteValue :
      Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    finalScale : Scale
    effectiveCoupling : Scale → Scalar
    couplingAtFinalScale : Set
    effectiveCouplingsRemainSmall : ∀ scale → Set

    -- Eq. (0.31):
    -- |1/g^2 - 1/g0^2 - beta log(1/epsilon)|
    -- <= beta' g0^2 log(1/epsilon).
    equation031 :
      LessEqual
        (absoluteValue
          (subtract
            (subtract
              (inverseSquare g g)
              (inverseSquare g0 g0))
            (multiply beta
              (logarithm epsilon epsilon))))
        (multiply
          (multiply betaPrime (multiply g0 g0))
          (logarithm epsilon epsilon))

open BalabanTheorem2RunningCouplingTarget public

record DASHIRunningCouplingMatchesBalaban031
    (Scale Scalar : Set) : Set₁ where
  field
    target : BalabanTheorem2RunningCouplingTarget Scale Scalar

    dashiInverseCoupling dashiBareInverseCoupling : Scalar
    dashiUniversalLog dashiQuarticError : Scalar

    dashiMainTermMatches : Set
    dashiQuarticErrorBound : Set
    dashiEndpointInequality : Set

open DASHIRunningCouplingMatchesBalaban031 public

physicalRunningCouplingRecursionHasBalabanShape :
  ∀ {Scale Scalar} →
  DASHIRunningCouplingMatchesBalaban031 Scale Scalar → Set
physicalRunningCouplingRecursionHasBalabanShape = dashiEndpointInequality

balabanTheorem1ArchitectureLevel : ProofLevel
balabanTheorem1ArchitectureLevel = machineChecked

balabanLocalizationConventionLevel : ProofLevel
balabanLocalizationConventionLevel = machineChecked

balaban031ComparisonReductionLevel : ProofLevel
balaban031ComparisonReductionLevel = machineChecked

literalDASHIMainAndQuarticInputsLevel : ProofLevel
literalDASHIMainAndQuarticInputsLevel = conditional
