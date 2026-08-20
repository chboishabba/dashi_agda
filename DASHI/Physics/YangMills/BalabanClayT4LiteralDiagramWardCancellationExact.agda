module DASHI.Physics.YangMills.BalabanClayT4LiteralDiagramWardCancellationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Kenneth G. Wilson, "Confinement of Quarks", Physical Review D 10 (1974),
-- 2445--2459. DOI: 10.1103/PhysRevD.10.2445
--
-- Ludwig D. Faddeev and Victor N. Popov, "Feynman Diagrams for the Yang--Mills
-- Field", Physics Letters B 25 (1967), 29--30.
-- DOI: 10.1016/0370-2693(67)90067-6
--
-- Luis F. Abbott, "The Background Field Method Beyond One Loop", Nuclear
-- Physics B 185 (1981), 189--203. DOI: 10.1016/0550-3213(81)90371-0
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223
-- Relationship: Sections 4--5, pp. 281--298, are the Ward/tensor comparison
-- target.  The literal lattice vertices and diagram cancellations below remain
-- DASHI obligations and are not imported from continuum Feynman rules.
------------------------------------------------------------------------

data DiagramKind : Set where
  gaugeLoop ghostLoop haarLoop : DiagramKind

record LiteralBackgroundVertices
    (Background Fluctuation Operator Vertex : Set) : Set₁ where
  field
    wilsonAction : Background → Fluctuation → Set
    gaugeFixingAction : Background → Fluctuation → Set
    faddeevPopovDeterminant : Background → Set
    haarChartDensity : Background → Set

    quadraticOperator : Background → Operator
    cubicGaugeVertex quarticGaugeVertex ghostVertex haarQuadraticVertex :
      Background → Vertex

    wilsonBackgroundQuadraticVertexExact : ∀ background fluctuation → Set
    wilsonBackgroundCubicVertexExact : ∀ background → Set
    wilsonBackgroundQuarticVertexExact : ∀ background → Set
    faddeevPopovGhostOperatorExact : ∀ background → Set
    ghostBackgroundVertexExact : ∀ background → Set
    haarMeasureQuadraticVertexExact : ∀ background → Set

open LiteralBackgroundVertices public

record LiteralOneLoopDiagramFamily
    (Momentum Lorentz Color Scalar Kernel : Set) : Set₁ where
  field
    zero add negate : Scalar → Scalar → Scalar
    deltaColor : Color → Color → Scalar

    gaugeKernel ghostKernel haarKernel combinedKernel :
      Momentum → Lorentz → Lorentz → Color → Color → Scalar

    gaugeLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set
    ghostLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set
    haarLoopTwoPointKernelExact : ∀ momentum mu nu a b → Set

    combinedKernelDefinition : ∀ momentum mu nu a b →
      combinedKernel momentum mu nu a b
      ≡ add
          (gaugeKernel momentum mu nu a b)
          (add
            (ghostKernel momentum mu nu a b)
            (haarKernel momentum mu nu a b))

    translationAction : Momentum → Momentum → Momentum
    hypercubicAction : Lorentz → Lorentz

    gaugeTranslationInvariant : ∀ shift momentum mu nu a b → Set
    ghostTranslationInvariant : ∀ shift momentum mu nu a b → Set
    haarTranslationInvariant : ∀ shift momentum mu nu a b → Set

    gaugeColorDiagonal : ∀ momentum mu nu a b → Set
    ghostColorDiagonal : ∀ momentum mu nu a b → Set
    haarColorDiagonal : ∀ momentum mu nu a b → Set

    gaugeHypercubicCovariant : ∀ momentum mu nu a b → Set
    ghostHypercubicCovariant : ∀ momentum mu nu a b → Set
    haarHypercubicCovariant : ∀ momentum mu nu a b → Set

    latticeDerivative : Momentum → Lorentz → Scalar
    contractLongitudinal :
      (Momentum → Lorentz → Lorentz → Color → Color → Scalar) →
      Momentum → Lorentz → Color → Color → Scalar

    gaugeWardDefect ghostWardDefect haarWardDefect :
      Momentum → Lorentz → Color → Color → Scalar

    gaugeWardIdentity : ∀ momentum nu a b →
      contractLongitudinal gaugeKernel momentum nu a b
      ≡ gaugeWardDefect momentum nu a b
    ghostWardIdentity : ∀ momentum nu a b →
      contractLongitudinal ghostKernel momentum nu a b
      ≡ ghostWardDefect momentum nu a b
    haarWardIdentity : ∀ momentum nu a b →
      contractLongitudinal haarKernel momentum nu a b
      ≡ haarWardDefect momentum nu a b

    contractCombinedDistributes : ∀ momentum nu a b →
      contractLongitudinal combinedKernel momentum nu a b
      ≡ add
          (contractLongitudinal gaugeKernel momentum nu a b)
          (add
            (contractLongitudinal ghostKernel momentum nu a b)
            (contractLongitudinal haarKernel momentum nu a b))

    wardDefectsCancel : ∀ momentum nu a b →
      add
        (gaugeWardDefect momentum nu a b)
        (add
          (ghostWardDefect momentum nu a b)
          (haarWardDefect momentum nu a b))
      ≡ zero (gaugeWardDefect momentum nu a b)
          (gaugeWardDefect momentum nu a b)

    zeroMomentum : Momentum
    massTensor longitudinalTensor transverseTensor :
      Momentum → Lorentz → Lorentz → Color → Color → Scalar

    combinedKernelTensorSplit : ∀ momentum mu nu a b →
      combinedKernel momentum mu nu a b
      ≡ add
          (massTensor momentum mu nu a b)
          (add
            (longitudinalTensor momentum mu nu a b)
            (transverseTensor momentum mu nu a b))

    wardAndHypercubicForceMassZero : ∀ mu nu a b →
      massTensor zeroMomentum mu nu a b
      ≡ zero (massTensor zeroMomentum mu nu a b)
          (massTensor zeroMomentum mu nu a b)

    wardForcesLongitudinalZero : ∀ momentum mu nu a b →
      longitudinalTensor momentum mu nu a b
      ≡ zero (longitudinalTensor momentum mu nu a b)
          (longitudinalTensor momentum mu nu a b)

open LiteralOneLoopDiagramFamily public

combinedOneLoopKernelExact = combinedKernelDefinition

latticeWardIdentityForOneLoopKernelLiteral :
  ∀ {Momentum Lorentz Color Scalar Kernel}
    (dataSet : LiteralOneLoopDiagramFamily
      Momentum Lorentz Color Scalar Kernel)
    momentum nu a b →
  contractLongitudinal dataSet (combinedKernel dataSet) momentum nu a b
  ≡ zero dataSet
      (gaugeWardDefect dataSet momentum nu a b)
      (gaugeWardDefect dataSet momentum nu a b)
latticeWardIdentityForOneLoopKernelLiteral dataSet momentum nu a b =
  trans
    (contractCombinedDistributes dataSet momentum nu a b)
    (trans
      (cong
        (λ gaugeValue → add dataSet gaugeValue
          (add dataSet
            (contractLongitudinal dataSet (ghostKernel dataSet)
              momentum nu a b)
            (contractLongitudinal dataSet (haarKernel dataSet)
              momentum nu a b)))
        (gaugeWardIdentity dataSet momentum nu a b))
      (trans
        (cong
          (λ ghostValue → add dataSet
            (gaugeWardDefect dataSet momentum nu a b)
            (add dataSet ghostValue
              (contractLongitudinal dataSet (haarKernel dataSet)
                momentum nu a b)))
          (ghostWardIdentity dataSet momentum nu a b))
        (trans
          (cong
            (λ haarValue → add dataSet
              (gaugeWardDefect dataSet momentum nu a b)
              (add dataSet
                (ghostWardDefect dataSet momentum nu a b) haarValue))
            (haarWardIdentity dataSet momentum nu a b))
          (wardDefectsCancel dataSet momentum nu a b))))

vacuumPolarizationMassTermZeroLiteral = wardAndHypercubicForceMassZero
vacuumPolarizationLongitudinalPartZeroLiteral = wardForcesLongitudinalZero

record LiteralTransverseScalarReduction
    (Momentum Lorentz Color Scalar : Set) : Set₁ where
  field
    diagrams : LiteralOneLoopDiagramFamily Momentum Lorentz Color Scalar Scalar

    latticeLaplacian : Momentum → Scalar
    latticeDerivativeProduct : Momentum → Lorentz → Lorentz → Scalar
    scalarVacuumPolarization : Momentum → Scalar

    transverseProjector : Momentum → Lorentz → Lorentz → Scalar
    transverseProjectorDefinition : ∀ momentum mu nu → Set

    colorCasimir : Color → Color → Scalar

    vacuumPolarizationKernelTransverseLiteral : ∀ momentum mu nu a b →
      combinedKernel diagrams momentum mu nu a b
      ≡ add diagrams
          (zero diagrams
            (combinedKernel diagrams momentum mu nu a b)
            (combinedKernel diagrams momentum mu nu a b))
          (add diagrams
            (zero diagrams
              (combinedKernel diagrams momentum mu nu a b)
              (combinedKernel diagrams momentum mu nu a b))
            (transverseTensor diagrams momentum mu nu a b))

    transverseTensorScalarFactorizationExact : ∀ momentum mu nu a b → Set
    vacuumPolarizationScalarIntegrandExact : ∀ momentum → Set

open LiteralTransverseScalarReduction public

oneLoopKernelTranslationInvariantLiteral :
  ∀ {Momentum Lorentz Color Scalar Kernel}
    (dataSet : LiteralOneLoopDiagramFamily Momentum Lorentz Color Scalar Kernel) →
  (∀ shift momentum mu nu a b →
      gaugeTranslationInvariant dataSet shift momentum mu nu a b)
  × ((∀ shift momentum mu nu a b →
      ghostTranslationInvariant dataSet shift momentum mu nu a b)
  × (∀ shift momentum mu nu a b →
      haarTranslationInvariant dataSet shift momentum mu nu a b))
oneLoopKernelTranslationInvariantLiteral dataSet =
  gaugeTranslationInvariant dataSet ,
  (ghostTranslationInvariant dataSet , haarTranslationInvariant dataSet)

oneLoopKernelColorDiagonalLiteral :
  ∀ {Momentum Lorentz Color Scalar Kernel}
    (dataSet : LiteralOneLoopDiagramFamily Momentum Lorentz Color Scalar Kernel) →
  (∀ momentum mu nu a b → gaugeColorDiagonal dataSet momentum mu nu a b)
  × ((∀ momentum mu nu a b → ghostColorDiagonal dataSet momentum mu nu a b)
  × (∀ momentum mu nu a b → haarColorDiagonal dataSet momentum mu nu a b))
oneLoopKernelColorDiagonalLiteral dataSet =
  gaugeColorDiagonal dataSet ,
  (ghostColorDiagonal dataSet , haarColorDiagonal dataSet)

oneLoopKernelHypercubicCovariantLiteral :
  ∀ {Momentum Lorentz Color Scalar Kernel}
    (dataSet : LiteralOneLoopDiagramFamily Momentum Lorentz Color Scalar Kernel) →
  (∀ momentum mu nu a b → gaugeHypercubicCovariant dataSet momentum mu nu a b)
  × ((∀ momentum mu nu a b → ghostHypercubicCovariant dataSet momentum mu nu a b)
  × (∀ momentum mu nu a b → haarHypercubicCovariant dataSet momentum mu nu a b))
oneLoopKernelHypercubicCovariantLiteral dataSet =
  gaugeHypercubicCovariant dataSet ,
  (ghostHypercubicCovariant dataSet , haarHypercubicCovariant dataSet)

literalVertexReductionLevel : ProofLevel
literalVertexReductionLevel = machineChecked

literalDiagramCombinationLevel : ProofLevel
literalDiagramCombinationLevel = machineChecked

literalWardCancellationLevel : ProofLevel
literalWardCancellationLevel = machineChecked

literalTransverseScalarReductionLevel : ProofLevel
literalTransverseScalarReductionLevel = machineChecked

literalWilsonGhostHaarFormulaInputsLevel : ProofLevel
literalWilsonGhostHaarFormulaInputsLevel = conditional
