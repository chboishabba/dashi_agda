module DASHI.Physics.YangMills.BalabanClayT3LiteralPointwiseHessianEstimatesExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Propagators for Lattice Gauge Theories in a Background
-- Field", Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355
-- Relationship: literal background Hessian, covariant transport and local
-- propagator perturbation architecture.
--
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Communications in Mathematical Physics 98 (1985), 17--51.
-- DOI: 10.1007/BF01211042
-- Relationship: nonlinear block-average derivative and path telescoping.
--
-- DASHI contribution: every pointwise remainder is decomposed into a finite atom
-- list.  Global constants are allowed to consume only the atomwise estimates and
-- explicit incidence charges, not a pre-packaged physical endpoint.
------------------------------------------------------------------------

sumℚ : List ℚ → ℚ
sumℚ [] = 0ℚ
sumℚ (x ∷ xs) = x + sumℚ xs

record FinitePointwiseExpansion
    (Background State Cell Atom : Set) : Set₁ where
  field
    atoms : Background → State → Cell → List Atom
    atomValue atomMajorant : Background → State → Cell → Atom → ℚ
    localRemainder localCharge radius coefficient :
      Background → State → Cell → ℚ

    mappedValues mappedMajorants :
      Background → State → Cell → List Atom → List ℚ
    mappedValuesEmpty : ∀ background state cell →
      mappedValues background state cell [] ≡ []
    mappedValuesStep : ∀ background state cell atom rest →
      mappedValues background state cell (atom ∷ rest)
      ≡ atomValue background state cell atom
        ∷ mappedValues background state cell rest
    mappedMajorantsEmpty : ∀ background state cell →
      mappedMajorants background state cell [] ≡ []
    mappedMajorantsStep : ∀ background state cell atom rest →
      mappedMajorants background state cell (atom ∷ rest)
      ≡ atomMajorant background state cell atom
        ∷ mappedMajorants background state cell rest

    expansionExact : ∀ background state cell →
      localRemainder background state cell
      ≡ sumℚ (mappedValues background state cell (atoms background state cell))

    atomAbsoluteBound : ∀ background state cell atom →
      atomValue background state cell atom
      ≤ atomMajorant background state cell atom

    finiteAtomSumBound : ∀ background state cell →
      sumℚ (mappedValues background state cell (atoms background state cell))
      ≤ sumℚ (mappedMajorants background state cell (atoms background state cell))

    majorantSumBelowConfiguredCharge : ∀ background state cell →
      sumℚ (mappedMajorants background state cell (atoms background state cell))
      ≤ coefficient background state cell
        * radius background state cell
        * localCharge background state cell

    transitive : ∀ {left middle right : ℚ} →
      left ≤ middle → middle ≤ right → left ≤ right

open FinitePointwiseExpansion public

finitePointwiseExpansionBound :
  ∀ {Background State Cell Atom}
    (dataSet : FinitePointwiseExpansion Background State Cell Atom)
    background state cell →
  localRemainder dataSet background state cell
  ≤ coefficient dataSet background state cell
    * radius dataSet background state cell
    * localCharge dataSet background state cell
finitePointwiseExpansionBound dataSet background state cell =
  subst
    (λ lower → lower
      ≤ coefficient dataSet background state cell
        * radius dataSet background state cell
        * localCharge dataSet background state cell)
    (expansionExact dataSet background state cell)
    (transitive dataSet
      (finiteAtomSumBound dataSet background state cell)
      (majorantSumBelowConfiguredCharge dataSet background state cell))

record PlaquetteCurvaturePointwiseData
    (Background State Plaquette Atom : Set) : Set₁ where
  field
    expansion : FinitePointwiseExpansion Background State Plaquette Atom
    wilsonPlaquetteSecondVariationAtBackgroundExact :
      ∀ background state plaquette → Set
    wilsonPlaquetteSecondVariationAtIdentityExact :
      ∀ state plaquette → Set
    plaquetteCurvatureDifferenceExact :
      ∀ background state plaquette → Set
    su2BracketCrossProductExact : ∀ background state plaquette atom → Set
    plaquetteHasFourOrientedEdges : ∀ plaquette → Set
    positiveEdgeOccursInSixPlaquettes : Set

open PlaquetteCurvaturePointwiseData public

plaquetteCurvaturePointwiseBound dataSet =
  finitePointwiseExpansionBound (expansion dataSet)

record TransportPointwiseData
    (Background State Edge Atom : Set) : Set₁ where
  field
    expansion : FinitePointwiseExpansion Background State Edge Atom
    covariantForwardDifferenceExact : ∀ background state edge → Set
    adjointTransportMinusIdentityExact : ∀ background state edge → Set
    adjointTransportChordalBound : ∀ background state edge → Set
    transportedEdgeDifferenceExact : ∀ background state edge → Set
    orientedEdgeIncidenceExact : Set

open TransportPointwiseData public

adjointTransportPointwiseBound dataSet =
  finitePointwiseExpansionBound (expansion dataSet)
transportedEdgeDifferenceBound = adjointTransportPointwiseBound

record ChartMetricPointwiseData
    (Background State Link Atom : Set) : Set₁ where
  field
    expansion : FinitePointwiseExpansion Background State Link Atom
    rightJacobianMetricExact : ∀ background link → Set
    rightJacobianInverseMetricExact : ∀ background link → Set
    pulledBackMetricUsesInverseTransposeInverse : ∀ background link → Set
    chartMetricMinusIdentityExact : ∀ background link → Set
    correctedPerpendicularSingularValueExact : ∀ background link → Set

open ChartMetricPointwiseData public

chartMetricQuadraticFormBound dataSet =
  finitePointwiseExpansionBound (expansion dataSet)
chartPointwiseHessianBound = chartMetricQuadraticFormBound

record GaugeDivergencePointwiseData
    (Background State Site Atom : Set) : Set₁ where
  field
    expansion : FinitePointwiseExpansion Background State Site Atom
    backgroundCovariantDivergenceExact : ∀ background state site → Set
    covariantDivergenceMinusReferenceExact : ∀ background state site → Set
    gaugeFixingQuadraticDifferenceExact : ∀ background state site → Set
    fixedYoungParameterExact : Set
    gaugeYoungInequalityBound : ∀ background state site → Set
    siteHasEightOrientedEdges : Set

open GaugeDivergencePointwiseData public

covariantDivergencePointwiseBound dataSet =
  finitePointwiseExpansionBound (expansion dataSet)
gaugeIncidenceSumBound = covariantDivergencePointwiseBound

record BlockDerivativePointwiseData
    (Background State Block Atom : Set) : Set₁ where
  field
    expansion : FinitePointwiseExpansion Background State Block Atom
    nonlinearBlockAverageDerivativeExact : ∀ background state block → Set
    referenceBlockAverageDerivativeExact : ∀ state block → Set
    blockPathTransportTelescopingExact : ∀ background state block → Set
    canonicalBoolean4PathLengthAtMostFour : Set
    blockPenaltyQuadraticDifferenceExact : ∀ background state block → Set

open BlockDerivativePointwiseData public

blockDerivativeDifferencePointwiseBound dataSet =
  finitePointwiseExpansionBound (expansion dataSet)
constraintLocalChargeBound = blockDerivativeDifferencePointwiseBound

record LiteralFivePointwiseHessianPackage
    (Background State Plaquette Edge Link Site Block
      CurvatureAtom TransportAtom ChartAtom GaugeAtom ConstraintAtom : Set) : Set₂ where
  field
    curvature : PlaquetteCurvaturePointwiseData
      Background State Plaquette CurvatureAtom
    transport : TransportPointwiseData
      Background State Edge TransportAtom
    chart : ChartMetricPointwiseData
      Background State Link ChartAtom
    gauge : GaugeDivergencePointwiseData
      Background State Site GaugeAtom
    constraint : BlockDerivativePointwiseData
      Background State Block ConstraintAtom

open LiteralFivePointwiseHessianPackage public

allFivePointwiseEstimates dataSet =
  plaquetteCurvaturePointwiseBound (curvature dataSet) ,
  adjointTransportPointwiseBound (transport dataSet) ,
  chartMetricQuadraticFormBound (chart dataSet) ,
  covariantDivergencePointwiseBound (gauge dataSet) ,
  blockDerivativeDifferencePointwiseBound (constraint dataSet)
  where open import Data.Product using (_,_)

finiteAtomExpansionReductionLevel : ProofLevel
finiteAtomExpansionReductionLevel = machineChecked

literalCurvatureTransportChartReductionLevel : ProofLevel
literalCurvatureTransportChartReductionLevel = machineChecked

literalGaugeConstraintReductionLevel : ProofLevel
literalGaugeConstraintReductionLevel = machineChecked

literalPlaquetteTransportChartDivergenceBlockInputsLevel : ProofLevel
literalPlaquetteTransportChartDivergenceBlockInputsLevel = conditional
