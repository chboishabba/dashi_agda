module DASHI.Physics.Closure.NSShellSchurInstance where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.BlockSchurCoercivity

------------------------------------------------------------------------
-- Navier--Stokes shell instance.
--
-- Low/high shell transfer is written as
--
--   A = I - K00
--   B = K01
--   C = K10
--   D = I - K11
--   S = D - C A⁻¹ B.
--
-- This record contains only the block structure and the exact quadratic
-- identity.  The diagonal and cross-shell estimates are separate theorem
-- inputs, so the live analytic frontier cannot be hidden inside the model.
------------------------------------------------------------------------

record NSShellSchurStructure
    {v s : Level}
    (ShellVector : Set v)
    (Scalar : Set s)
    (O : SchurOrderLaws Scalar) : Set (lsuc (v ⊔ s)) where
  field
    identity : ShellVector → ShellVector
    k00 k01 k10 k11 : ShellVector → ShellVector
    lowInverse : ShellVector → ShellVector

    subtractVector :
      (ShellVector → ShellVector) →
      (ShellVector → ShellVector) →
      ShellVector → ShellVector

    composeVector :
      (ShellVector → ShellVector) →
      (ShellVector → ShellVector) →
      ShellVector → ShellVector

    lowBlock : ShellVector → ShellVector
    lowBlockDefinition : lowBlock ≡ subtractVector identity k00

    highBlock : ShellVector → ShellVector
    highBlockDefinition : highBlock ≡ subtractVector identity k11

    crossCorrection : ShellVector → ShellVector
    crossCorrectionDefinition :
      crossCorrection ≡ composeVector k10 (composeVector lowInverse k01)

    schurComplement : ShellVector → ShellVector
    schurDefinition :
      schurComplement ≡ subtractVector highBlock crossCorrection

    inner : ShellVector → ShellVector → Scalar

    highGap : Scalar
    crossBudget : Scalar

    schurQuadraticIdentity :
      ∀ x →
      inner x (schurComplement x) ≡
      _⊖_ O
        (inner x (highBlock x))
        (inner x (crossCorrection x))

open NSShellSchurStructure public

record NSShellSchurBounds
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    {O : SchurOrderLaws Scalar}
    (I : NSShellSchurStructure ShellVector Scalar O) : Set (v ⊔ s) where
  field
    highShellGap :
      ∀ x → _≤_ O (highGap I) (inner I x (highBlock I x))

    crossShellBound :
      ∀ x →
      _≤_ O
        (inner I x (crossCorrection I x))
        (crossBudget I)

    crossBudgetBelowGap :
      _≤_ O (crossBudget I) (highGap I)

open NSShellSchurBounds public

nsQuantitativeSchur :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurStructure ShellVector Scalar O) →
  NSShellSchurBounds I →
  QuantitativeBlockSchur ShellVector Scalar O
nsQuantitativeSchur O I B = record
  { dBlock = highBlock I
  ; crossCorrection = crossCorrection I
  ; schurComplement = schurComplement I
  ; inner = inner I
  ; highGap = highGap I
  ; crossBudget = crossBudget I
  ; schurQuadraticIdentity = schurQuadraticIdentity I
  ; highBlockCoercive = highShellGap B
  ; crossCorrectionBounded = crossShellBound B
  ; crossBelowHighGap = crossBudgetBelowGap B
  }

nsShellSchurCoercive :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (B : NSShellSchurBounds I)
    (x : ShellVector) →
  _≤_ O
    (_⊖_ O (highGap I) (crossBudget I))
    (inner I x (schurComplement I x))
nsShellSchurCoercive O I B =
  schurCoercive O (nsQuantitativeSchur O I B)

record NSStrictFrameGap
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurStructure ShellVector Scalar O) : Set (lsuc (v ⊔ s)) where
  field
    StrictlyPositive : Scalar → Set s
    residualPositive :
      StrictlyPositive (_⊖_ O (highGap I) (crossBudget I))

open NSStrictFrameGap public

nsStrictFrameGapCertificate :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurStructure ShellVector Scalar O)
    (B : NSShellSchurBounds I) →
  NSStrictFrameGap O I →
  QuantitativeSchurCertificate O (nsQuantitativeSchur O I B)
nsStrictFrameGapCertificate O I B G =
  certifyQuantitativeSchur O (nsQuantitativeSchur O I B) record
    { StrictlyPositive = StrictlyPositive G
    ; residualGapPositive = residualPositive G
    }
