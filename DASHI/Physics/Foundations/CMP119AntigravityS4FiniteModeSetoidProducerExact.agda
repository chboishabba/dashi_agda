{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityS4FiniteModeSetoidProducerExact where

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base using (ℚ)

import Real as Bishop

import DASHI.Physics.Foundations.CMP119AntigravityCanonicalRowABetaDrivenStateExact as RowAState
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalS4SetoidPhysicalPackageExact as S4
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravityFiniteModePlaquetteBetaSameObjectExact as Plaquette
import DASHI.Physics.Foundations.CMP119AntigravityP3GSetoidPhysicalCoreExact as Core
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeDecompositionExact as Decomposition
import DASHI.Physics.Foundations.CMP119AntigravityRichBrillouinFiniteModeGaussianProjectionExact as Gaussian
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinBoxReceiptFamilyExact as Rich
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Literal
import DASHI.Physics.YangMills.BalabanYM4BetaSplitPositivityExact as Split
import DASHI.Physics.YangMills.BalabanYM4FiniteModeBetaToSourceTrajectoryExact as FiniteMode
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow

------------------------------------------------------------------------
-- Concrete finite-mode route to S4. Both the CMP109 total beta weld and the
-- rich Gaussian projection are compiled from ONE finite-mode source packet.
-- Physical component equality and shell/epsilon matching are still explicit
-- fields of that packet: no unconditional P3A--F identification is claimed.
------------------------------------------------------------------------

record S4FiniteModeSourcePacket
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {split : Split.FiniteLatticeBetaSplit trajectory}
    {Mode Atom : Set}
    (inputs : BetaFlow.BetaDrivenCompleteDensityInputs
      {trajectory = trajectory} {split = split})
    (rowA : RowA.FiniteQuarticResponseConstants)
    (smallFieldCap largeFieldCap covarianceCap : ℚ)
    (finiteMode :
      FiniteMode.FiniteModeBetaTrajectoryData trajectory Mode Atom)
    (oneLoop : Literal.OneLoopVacuumPolarizationData Nat)
    (remainder : Literal.PlaquetteRemainderData Nat)
    (rich : Rich.LiteralBrillouinIntegralPhysicalData Nat Bishop.ℝ) : Set₂ where
  field
    betaCoordinates :
      RowAState.CanonicalRowABetaDrivenCoordinates
        inputs rowA smallFieldCap largeFieldCap covarianceCap

    finiteModeAndRich :
      Gaussian.RichBrillouinFiniteModeGaussianSameObject
        finiteMode oneLoop remainder rich

    traceBoundary :
      SU2.CanonicalBishopSU2TraceBoundary

open S4FiniteModeSourcePacket public

asSetoidPhysicalPackage :
  ∀ {trajectory split Mode Atom inputs rowA
       smallFieldCap largeFieldCap covarianceCap
       finiteMode oneLoop remainder rich} →
  S4FiniteModeSourcePacket
    {trajectory = trajectory} {split = split}
    {Mode = Mode} {Atom = Atom}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
    finiteMode oneLoop remainder rich →
  S4.CanonicalS4SetoidPhysicalPackage
    {trajectory = trajectory} {split = split}
    inputs rowA smallFieldCap largeFieldCap covarianceCap
asSetoidPhysicalPackage
    {rich = rich} source = record
  { S4.CanonicalS4SetoidPhysicalPackage.betaCoordinates =
      betaCoordinates source
  ; S4.CanonicalS4SetoidPhysicalPackage.coefficientWeld =
      Plaquette.asCMP109LiteralPlaquetteCoefficientWeld
        (Gaussian.finiteModePlaquette (finiteModeAndRich source))
  ; S4.CanonicalS4SetoidPhysicalPackage.rich = rich
  ; S4.CanonicalS4SetoidPhysicalPackage.geometry = record
      { Core.P3GSetoidPhysicalGeometry.richAddIsBishopAdd =
          Decomposition.richAddIsBishopAdd
            (Gaussian.decompositionAt (finiteModeAndRich source) zero)
      ; Core.P3GSetoidPhysicalGeometry.gaussianProjection =
          Gaussian.asRichBrillouinRationalGaussianProjection
            (finiteModeAndRich source)
      }
  ; S4.CanonicalS4SetoidPhysicalPackage.traceBoundary =
      traceBoundary source
  }
