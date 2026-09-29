{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3GNativeSetoidLiteralEvaluatorExact where

open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (_*_)
import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCMP109TrajectoryPlaquetteConstructorExact as Constructor
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as FinitePlaquette
import DASHI.Physics.Foundations.CMP119AntigravityLiteralEvaluatorFiniteModeSameObjectExact as LegacyEvaluator
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeDecompositionExact as Decomposition
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeGaussianProjectionExact as Gaussian
import DASHI.Physics.Foundations.CMP119AntigravityRichRegularLiteralEvaluatorSameObjectExact as Receipt
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as LegacyRunning
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as LiteralEvaluator
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaLowerRemainderExact as Local
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Genuine setoid-native evaluator source: NO P3.RunningCouplingRecursion and
-- NO CanonicalBishopSU2RunningInputs are arguments or fields.
--
-- The universal shell is specified in Bishop's _≃_ against the SAME finite-
-- mode ell. The full rich coefficient is compiled from shell and epsilon.
-- An adapter back from the legacy evaluator exists, but is not prerequisite.
------------------------------------------------------------------------

record NativeSetoidLiteralEvaluatorSource
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom expressions ward scalarData : Set}
    (finiteMode : FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Plaquette.OneLoopVacuumPolarizationData Nat)
    (remainder : Plaquette.PlaquetteRemainderData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₂ where
  field
    finiteModePlaquette :
      FinitePlaquette.FiniteModePlaquetteBetaSameObject
        finiteMode oneLoop remainder

    evaluatorAt :
      Nat → LiteralEvaluator.LiteralGeneratedBoxEvaluator
        expressions ward scalarData

    partitionSameEvaluator : ∀ k →
      Receipt.RichRegularLiteralEvaluatorSameObject rich k (evaluatorAt k)

    richAddIsBishopAdd :
      ∀ left right →
      Bishop._≃_
        (Rich.add rich left right)
        (Bishop._+_ left right)

    shellMatchesFiniteMode :
      ∀ k →
      Bishop._≃_
        (Rich.scalarIntegral rich k)
        (UV.embed
          (Local.oneLoopSU2Factor
            * Local.ell (FiniteMode.gaussianAt finiteMode k)))

    regularMatchesFiniteMode :
      ∀ k →
      Bishop._≃_
        (Rich.regularRemainder rich k)
        (UV.embed (Local.epsilon (FiniteMode.gaussianAt finiteMode k)))

open NativeSetoidLiteralEvaluatorSource public

asFiniteModeGaussian :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder rich} →
  NativeSetoidLiteralEvaluatorSource
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
    {expressions = expressions} {ward = ward} {scalarData = scalarData}
    finiteMode oneLoop remainder rich →
  Gaussian.RichBrillouinFiniteModeGaussianSameObject
    finiteMode oneLoop remainder rich
asFiniteModeGaussian source = record
  { Gaussian.RichBrillouinFiniteModeGaussianSameObject.finiteModePlaquette =
      finiteModePlaquette source
  ; Gaussian.RichBrillouinFiniteModeGaussianSameObject.decompositionAt =
      λ k → record
        { Decomposition.RichBrillouinFiniteModeDecomposition.richAddIsBishopAdd =
            richAddIsBishopAdd source
        ; Decomposition.RichBrillouinFiniteModeDecomposition.shellSameFiniteUniversalTerm =
            shellMatchesFiniteMode source k
        ; Decomposition.RichBrillouinFiniteModeDecomposition.regularMatchingSameFiniteEpsilon =
            regularMatchesFiniteMode source k
        }
  }

asPhysicalGeometry :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder rich}
    (source : NativeSetoidLiteralEvaluatorSource
      {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
      {expressions = expressions} {ward = ward} {scalarData = scalarData}
      finiteMode oneLoop remainder rich) →
  Core.P3GSetoidPhysicalGeometry
    (FinitePlaquette.asCMP109LiteralPlaquetteCoefficientWeld
      (finiteModePlaquette source))
    rich
asPhysicalGeometry source = record
  { Core.P3GSetoidPhysicalGeometry.richAddIsBishopAdd =
      richAddIsBishopAdd source
  ; Core.P3GSetoidPhysicalGeometry.gaussianProjection =
      Gaussian.asRichBrillouinRationalGaussianProjection
        (asFiniteModeGaussian source)
  }

-- Compatibility is one-way: old conventions can populate the native source,
-- but the native physical recurrence never needs to manufacture an intensional
-- equality proof to be consumed by S4.
fromLegacyEvaluator :
  ∀ {trajectory Mode Atom expressions ward scalarData
       finiteMode oneLoop remainder rich running}
    (legacy :
      LegacyEvaluator.LiteralEvaluatorFiniteModeSameObject
        {trajectory = trajectory} {Mode = Mode} {Atom = Atom}
        {expressions = expressions} {ward = ward} {scalarData = scalarData}
        finiteMode oneLoop remainder rich running) →
  NativeSetoidLiteralEvaluatorSource
    finiteMode oneLoop remainder rich
fromLegacyEvaluator legacy = record
  { NativeSetoidLiteralEvaluatorSource.finiteModePlaquette =
      LegacyEvaluator.finiteModePlaquette legacy
  ; NativeSetoidLiteralEvaluatorSource.evaluatorAt =
      LegacyEvaluator.evaluatorAt legacy
  ; NativeSetoidLiteralEvaluatorSource.partitionSameEvaluator =
      LegacyEvaluator.partitionSameLiteralEvaluator legacy
  ; NativeSetoidLiteralEvaluatorSource.richAddIsBishopAdd =
      LegacyEvaluator.richAddIsBishopAdd legacy
  ; NativeSetoidLiteralEvaluatorSource.shellMatchesFiniteMode =
      λ k →
        Decomposition.shellSameFiniteUniversalTerm
          (LegacyEvaluator.decompositionAt legacy k)
  ; NativeSetoidLiteralEvaluatorSource.regularMatchesFiniteMode =
      LegacyEvaluator.regularMatchingSameFiniteEpsilon legacy
  }
