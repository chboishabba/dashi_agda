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
-- This module proves the Wall-1 frame-gap reduction once the diagonal high
-- gap and cross-shell correction budget are supplied.  It does not assume the
-- still-open Biot--Savart cross-shell estimate.
------------------------------------------------------------------------

record NSShellSchurInputs
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

    highShellGap :
      ∀ x → _≤_ O highGap (inner x (highBlock x))

    crossShellBound :
      ∀ x → _≤_ O (inner x (crossCorrection x)) crossBudget

    crossBudgetBelowGap :
      _≤_ O crossBudget highGap

open NSShellSchurInputs public

nsQuantitativeSchur :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar) →
  NSShellSchurInputs ShellVector Scalar O →
  QuantitativeBlockSchur ShellVector Scalar O
nsQuantitativeSchur O I = record
  { dBlock = highBlock I
  ; crossCorrection = crossCorrection I
  ; schurComplement = schurComplement I
  ; inner = inner I
  ; highGap = highGap I
  ; crossBudget = crossBudget I
  ; schurQuadraticIdentity = schurQuadraticIdentity I
  ; highBlockCoercive = highShellGap I
  ; crossCorrectionBounded = crossShellBound I
  ; crossBelowHighGap = crossBudgetBelowGap I
  }

nsShellSchurCoercive :
  ∀ {v s}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurInputs ShellVector Scalar O)
    (x : ShellVector) →
  _≤_ O
    (_⊖_ O (highGap I) (crossBudget I))
    (inner I x (schurComplement I x))
nsShellSchurCoercive O I = schurCoercive O (nsQuantitativeSchur O I)

record NSStrictFrameGap
    {v s : Level}
    {ShellVector : Set v}
    {Scalar : Set s}
    (O : SchurOrderLaws Scalar)
    (I : NSShellSchurInputs ShellVector Scalar O) : Set (v ⊔ s) where
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
    (I : NSShellSchurInputs ShellVector Scalar O) →
  NSStrictFrameGap O I →
  QuantitativeSchurCertificate O (nsQuantitativeSchur O I)
nsStrictFrameGapCertificate O I G =
  certifyQuantitativeSchur O (nsQuantitativeSchur O I) record
    { StrictlyPositive = StrictlyPositive G
    ; residualGapPositive = residualPositive G
    }
