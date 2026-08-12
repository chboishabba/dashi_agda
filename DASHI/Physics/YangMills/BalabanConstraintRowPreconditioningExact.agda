module DASHI.Physics.YangMills.BalabanConstraintRowPreconditioningExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Roger A. Horn; Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories", Communications in Mathematical Physics
-- 102 (1985), 277--309.
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Isolate a purely coordinate fact used by the source-scale L=13 Gate-I
-- normal problem.  Replacing a constraint map C by S o C, where S is an
-- invertible change of coordinates on the constraint codomain, does not change
-- its zero fibre, derivative kernel, tangent projector, or physical normal
-- correction.  Only multiplier coordinates change.
--
-- This is the exact algebra behind conditioning the normalized block-average
-- rows by 13^2=169.  It prevents a harmless row normalization from degrading
-- the quantitative normal floor while preserving the same physical constraint
-- manifold.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record InvertibleRowChange (Row : Set) : Set₁ where
  field
    forward backward : Row → Row
    backwardForward : ∀ row → backward (forward row) ≡ row
    forwardBackward : ∀ row → forward (backward row) ≡ row

open InvertibleRowChange public

preconditionConstraint :
  ∀ {X Row : Set} → InvertibleRowChange Row →
  (X → Row) → X → Row
preconditionConstraint change constraint x =
  forward change (constraint x)

record ZeroPreservingRowChange (Row : Set) (zero : Row)
    (change : InvertibleRowChange Row) : Set where
  field
    forwardZero : forward change zero ≡ zero
    backwardZero : backward change zero ≡ zero

open ZeroPreservingRowChange public

preconditionedZeroImpliesOriginalZero :
  ∀ {X Row : Set} {zero : Row}
    (change : InvertibleRowChange Row)
    (zeroChange : ZeroPreservingRowChange Row zero change)
    (constraint : X → Row) x →
  preconditionConstraint change constraint x ≡ zero →
  constraint x ≡ zero
preconditionedZeroImpliesOriginalZero change zeroChange constraint x equality =
  trans
    (sym (backwardForward change (constraint x)))
    (trans
      (cong (backward change) equality)
      (backwardZero zeroChange))

originalZeroImpliesPreconditionedZero :
  ∀ {X Row : Set} {zero : Row}
    (change : InvertibleRowChange Row)
    (zeroChange : ZeroPreservingRowChange Row zero change)
    (constraint : X → Row) x →
  constraint x ≡ zero →
  preconditionConstraint change constraint x ≡ zero
originalZeroImpliesPreconditionedZero change zeroChange constraint x equality =
  trans
    (cong (forward change) equality)
    (forwardZero zeroChange)

record SameZeroFibre {X Row : Set} (zero : Row)
    (left right : X → Row) : Set where
  field
    leftToRight : ∀ x → left x ≡ zero → right x ≡ zero
    rightToLeft : ∀ x → right x ≡ zero → left x ≡ zero

open SameZeroFibre public

invertibleConstraintRowChangePreservesZeroFibre :
  ∀ {X Row : Set} {zero : Row}
    (change : InvertibleRowChange Row)
    (zeroChange : ZeroPreservingRowChange Row zero change)
    (constraint : X → Row) →
  SameZeroFibre zero constraint (preconditionConstraint change constraint)
invertibleConstraintRowChangePreservesZeroFibre change zeroChange constraint = record
  { leftToRight = originalZeroImpliesPreconditionedZero change zeroChange constraint
  ; rightToLeft = preconditionedZeroImpliesOriginalZero change zeroChange constraint
  }

------------------------------------------------------------------------
-- Linearized kernel invariance.
------------------------------------------------------------------------

preconditionLinear :
  ∀ {V Row : Set} → InvertibleRowChange Row →
  (V → Row) → V → Row
preconditionLinear = preconditionConstraint

invertibleConstraintRowChangePreservesKernelForward :
  ∀ {V Row : Set} {zero : Row}
    (change : InvertibleRowChange Row)
    (zeroChange : ZeroPreservingRowChange Row zero change)
    (linear : V → Row) vector →
  linear vector ≡ zero →
  preconditionLinear change linear vector ≡ zero
invertibleConstraintRowChangePreservesKernelForward =
  originalZeroImpliesPreconditionedZero

invertibleConstraintRowChangePreservesKernelBackward :
  ∀ {V Row : Set} {zero : Row}
    (change : InvertibleRowChange Row)
    (zeroChange : ZeroPreservingRowChange Row zero change)
    (linear : V → Row) vector →
  preconditionLinear change linear vector ≡ zero →
  linear vector ≡ zero
invertibleConstraintRowChangePreservesKernelBackward =
  preconditionedZeroImpliesOriginalZero

------------------------------------------------------------------------
-- Normal correction and tangent projector invariance.
--
-- If N : Row -> V is the physical normal solve for the original row
-- coordinates, the same solve expressed in the new coordinates is N o S^-1.
-- Hence N' (S L v) = N (L v) exactly.  No matrix norm estimate is involved.
------------------------------------------------------------------------

preconditionedNormalCorrection :
  ∀ {V Row : Set} → InvertibleRowChange Row →
  (Row → V) → Row → V
preconditionedNormalCorrection change normal row =
  normal (backward change row)

preconditionedNormalOnLinearExact :
  ∀ {V Row : Set}
    (change : InvertibleRowChange Row)
    (normal : Row → V) (linear : V → Row) vector →
  preconditionedNormalCorrection change normal
    (preconditionLinear change linear vector)
  ≡ normal (linear vector)
preconditionedNormalOnLinearExact change normal linear vector =
  cong normal (backwardForward change (linear vector))

record Subtraction (V : Set) : Set₁ where
  field
    subtract : V → V → V

open Subtraction public

tangentProjector :
  ∀ {V Row : Set} → Subtraction V →
  (V → Row) → (Row → V) → V → V
tangentProjector algebra linear normal vector =
  subtract algebra vector (normal (linear vector))

preconditionedTangentProjectorExact :
  ∀ {V Row : Set}
    (algebra : Subtraction V)
    (change : InvertibleRowChange Row)
    (linear : V → Row) (normal : Row → V) vector →
  tangentProjector algebra
    (preconditionLinear change linear)
    (preconditionedNormalCorrection change normal)
    vector
  ≡ tangentProjector algebra linear normal vector
preconditionedTangentProjectorExact algebra change linear normal vector =
  cong (subtract algebra vector)
    (preconditionedNormalOnLinearExact change normal linear vector)

------------------------------------------------------------------------
-- Multiplier coordinates transform contragrediently.  At this abstraction
-- level the dual row change is supplied explicitly rather than silently
-- identifying a row carrier with its dual.
------------------------------------------------------------------------

transformMultiplier :
  ∀ {Multiplier : Set} → InvertibleRowChange Multiplier →
  Multiplier → Multiplier
transformMultiplier dualChange = backward dualChange

transformMultiplierRoundTrip :
  ∀ {Multiplier : Set}
    (dualChange : InvertibleRowChange Multiplier) multiplier →
  forward dualChange (transformMultiplier dualChange multiplier) ≡ multiplier
transformMultiplierRoundTrip dualChange multiplier =
  forwardBackward dualChange multiplier

constraintRowZeroFibreInvarianceLevel : ProofLevel
constraintRowZeroFibreInvarianceLevel = machineChecked

constraintRowKernelInvarianceLevel : ProofLevel
constraintRowKernelInvarianceLevel = machineChecked

constraintRowTangentProjectorInvarianceLevel : ProofLevel
constraintRowTangentProjectorInvarianceLevel = machineChecked
