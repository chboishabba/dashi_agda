module DASHI.Physics.YangMills.BalabanP0LiteralIndexedTensorWardSourceExact where

-- Source-indexed P0.4/P0.5 interface over the ACTUAL original four
-- DiagramExpression quotients from BalabanP0LiteralDiagramTopologyFromSource.
--
-- KEY CORRECTION: a longitudinal Ward contraction is a SUM over the
-- Lorentz index mu of the TENSOR Pi_{mu,nu}; it is not an arbitrary
-- endomorphism of one already contracted scalar AST.
--
-- All four `literalPhysicalTopology` entries at (mu,nu) are the
-- ORIGINAL Wilson bubble/tadpole/FP ghost/Haar quotient constructions.
-- Physical source owners must supply each indexed numerator and the
-- true lattice derivative, with the source's oriented link phases.
--
-- The full contraction and four individual sector contractions are
-- constructed, not invented numerical results. A physical Ward
-- cancellation theorem must IDENTIFY their interpreted values at
-- actual momentum points and prove the defects cancel.
--
-- DO NOT fill the old LiteralWardExpressionProofs by setting
-- longitudinalContract = constant 0: that would pass a syntactic
-- equality without showing anything about the original tensor.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (_∷_; [])
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanP0LiteralDiagramTopologyFromSourceExact as Diagrams

record PhysicalIndexedFourSource : Set₁ where
  field
    -- Physical Fourier numerator at the SAME source external momentum
    -- and both Lorentz indices, including the actual tensor contractions.
    numeratorSources :
      Eval.AxisIndex → Eval.AxisIndex →
      Diagrams.ActualPhysicalDiagramNumeratorSources

    -- Must be the true chosen lattice forward/backward derivative,
    -- including source phase and orientation factors when relevant.
    originalLatticeDerivative : Eval.AxisIndex → Eval.DiagramExpression
open PhysicalIndexedFourSource public

sourceDiagramAt :
  PhysicalIndexedFourSource →
  Eval.AxisIndex → Eval.AxisIndex →
  Eval.LiteralDiagramExpressions
sourceDiagramAt source mu nu =
  Diagrams.literalPhysicalTopology (numeratorSources source mu nu)

sourceBubbleAt source mu nu =
  Eval.gaugeBubble (sourceDiagramAt source mu nu)

sourceTadpoleAt source mu nu =
  Eval.gaugeTadpole (sourceDiagramAt source mu nu)

sourceGhostAt source mu nu =
  Eval.ghostLoop (sourceDiagramAt source mu nu)

sourceHaarAt source mu nu =
  Eval.haarLoop (sourceDiagramAt source mu nu)

sourceTensorAt :
  PhysicalIndexedFourSource →
  Eval.AxisIndex → Eval.AxisIndex → Eval.DiagramExpression
sourceTensorAt source mu nu =
  Eval.combinedKernelExpression (sourceDiagramAt source mu nu)

-- The selected tensor Ward contraction is the actual FOUR-index
-- finite source contraction, not `λ _ _ → rationalConstant 0`.
fourAxisContraction :
  (source : PhysicalIndexedFourSource) →
  (tensor : Eval.AxisIndex → Eval.AxisIndex → Eval.DiagramExpression) →
  Eval.AxisIndex → Eval.DiagramExpression
fourAxisContraction source tensor nu =
  Eval.sumExpressions
    (Eval.multiply (originalLatticeDerivative source Eval.axis0)
      (tensor Eval.axis0 nu) ∷
     Eval.multiply (originalLatticeDerivative source Eval.axis1)
      (tensor Eval.axis1 nu) ∷
     Eval.multiply (originalLatticeDerivative source Eval.axis2)
      (tensor Eval.axis2 nu) ∷
     Eval.multiply (originalLatticeDerivative source Eval.axis3)
      (tensor Eval.axis3 nu) ∷ [])

literalFullWardExpression :
  PhysicalIndexedFourSource →
  Eval.AxisIndex → Eval.DiagramExpression
literalFullWardExpression source =
  fourAxisContraction source (sourceTensorAt source)

literalGaugeBubbleWardExpression source =
  fourAxisContraction source (sourceBubbleAt source)

literalGaugeTadpoleWardExpression source =
  fourAxisContraction source (sourceTadpoleAt source)

literalGhostWardExpression source =
  fourAxisContraction source (sourceGhostAt source)

literalHaarWardExpression source =
  fourAxisContraction source (sourceHaarAt source)

-- Exact source syntax fact: the combined tensor is the ORIGINAL
-- four-quotient expression produced by the same source object.
sourceTensorIsOriginalFourTerms :
  ∀ source mu nu →
  sourceTensorAt source mu nu
  ≡ Eval.combinedKernelExpression
      (Diagrams.literalPhysicalTopology (numeratorSources source mu nu))
sourceTensorIsOriginalFourTerms source mu nu = refl

-- The correct next owner must supply semantic congruence and an actual
-- physical Ward defect-cancellation proof. The free syntax does NOT
-- equate `multiply derivative (add diagrams)` with the sum of four
-- separately contracted diagrams by definitional equality:
-- distributivity belongs to a *sound interpreted physical algebra*.
--
-- Source physical 4-sector Ward evidence remains OPEN and must connect
-- the existing P33 16-atom Wilson jets, reduced-FP trace-log and Haar
-- chart using actual Fourier momentum and axis phases. No artificial
-- `Set = ⊤` or trivial contraction shortcut is supplied.
