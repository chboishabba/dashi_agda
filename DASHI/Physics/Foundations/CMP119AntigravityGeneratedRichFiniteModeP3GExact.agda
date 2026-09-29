{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityGeneratedRichFiniteModeP3GExact where

------------------------------------------------------------------------
-- SELECTED LITERAL EVALUATOR -> NATIVE P3G WITHOUT PARTITION AXIOM.
--
-- A single generated evaluator fixes the 240-box regular partition and
-- four-orbit receipts definitionally. Its analytic shell and finite epsilon
-- matches are STILL proper physical proof obligations; the normalized beta
-- source lives on the same FiniteModeBetaTrajectoryData object.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_*_)
import Real as Bishop
import RealProperties as BishopP

import DASHI.Physics.Foundations.CMP119AntigravityGeneratedRichFromSelectedLiteralEvaluatorExact as Generated
import DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact as Native
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as PlaquetteSame
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as Finite
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette

record GeneratedSelectedFiniteModePhysicalWeld
  {trajectory Mode Atom expressions ward scalarData}
  (finiteMode : Finite.FiniteModeBetaTrajectoryData trajectory Mode Atom)
  (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
  (remainder : Plaquette.PlaquetteRemainderData Nat)
  {evaluatorAt}
  (selected :
    Generated.SelectedEvaluatorGeneratedRichSource
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      evaluatorAt) : Set₁ where
  field
    finiteModePlaquette :
      PlaquetteSame.FiniteModePlaquetteBetaSameObject
        finiteMode oneLoop remainder

    physicalShellMatchesFiniteEll : ∀ k →
      Bishop._≃_
        (Generated.scalarIntegral selected k)
        (UV.embed
          (Local.oneLoopSU2Factor * Local.ell
            (Finite.gaussianAt finiteMode k)))

    physicalRegularMatchesFiniteEpsilon : ∀ k →
      Bishop._≃_
        (Generated.regularRemainder selected k)
        (UV.embed
          (Local.epsilon (Finite.gaussianAt finiteMode k)))

open GeneratedSelectedFiniteModePhysicalWeld public

asNativeSelectedEvaluator :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder evaluatorAt selected} →
  GeneratedSelectedFiniteModePhysicalWeld
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder {evaluatorAt = evaluatorAt} selected →
  Native.NativeSetoidLiteralEvaluatorSource
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder (Generated.asGeneratedRich selected)
asNativeSelectedEvaluator {evaluatorAt = evaluatorAt} {selected = selected} physical = record
  { Native.NativeSetoidLiteralEvaluatorSource.finiteModePlaquette =
      finiteModePlaquette physical
  ; Native.NativeSetoidLiteralEvaluatorSource.evaluatorAt =
      evaluatorAt
  ; Native.NativeSetoidLiteralEvaluatorSource.partitionSameEvaluator =
      Generated.asSelectedPartitionSameObject selected
  ; Native.NativeSetoidLiteralEvaluatorSource.richAddIsBishopAdd =
      λ _ _ → BishopP.≃-refl
  ; Native.NativeSetoidLiteralEvaluatorSource.shellMatchesFiniteMode =
      physicalShellMatchesFiniteEll physical
  ; Native.NativeSetoidLiteralEvaluatorSource.regularMatchesFiniteMode =
      physicalRegularMatchesFiniteEpsilon physical
  }
