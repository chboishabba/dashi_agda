{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityP3UVAnchorFromSharedCouplingExact where

open import Agda.Builtin.Nat using (Nat; zero)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; 1ℚ; _*_; Positive)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopInverseSquareProductExact as Inverse
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalBishopSU2ConventionExact as SU2
import DASHI.Physics.Foundations.CMP119AntigravitySourceHistoryBishopUVViewExact as UV
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4BishopFourCornerIntervalExact as Embed
import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as BetaFlow
import DASHI.Physics.YangMills.Balaban1989FiniteModeInverseSquareTerminalHistoryExact as History
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- UV ANCHOR FROM THE SAME BARE/INITIAL COUPLING
--
-- The finite beta history already records, at every scale,
--
--   u_k * g_k^2 = 1
--
-- with g_k > 0.  Therefore at k=0 the embedded source inverse coupling is the
-- unique Bishop candidate cancelling the positive square of the SAME g_0.
-- If P3's initial inverseCouplingSq satisfies that same representation,
-- inverse uniqueness forces the desired UV anchor.
------------------------------------------------------------------------

square : Bishop.ℝ → Bishop.ℝ
square value = Bishop._*_ value value

embeddedCouplingPositive :
  ∀ coupling →
  Positive coupling →
  Bishop._<_ Bishop.0ℝ (Embed.embed coupling)
embeddedCouplingPositive coupling positive =
  Embed.embedStrictOrder (ℚP.positive⁻¹ positive)

embeddedSourceInverseCancelsCouplingSquare :
  ∀ {trajectory Mode Atom betaData}
    (history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData) →
  Bishop._≃_
    (Bishop._*_
      (UV.embed (Flow.inverseCoupling trajectory zero))
      (square (UV.embed (History.couplingAt history zero))))
    Bishop.1ℝ
embeddedSourceInverseCancelsCouplingSquare
    {trajectory = trajectory} history =
  let
    u = Flow.inverseCoupling trajectory zero
    g = History.couplingAt history zero
    sourceLaw = History.inverseCouplingRepresentation history zero
    embeddedProduct :
      Bishop._≃_
        (UV.embed (u * (g * g)))
        (Bishop._*_ (UV.embed u)
          (Bishop._*_ (UV.embed g) (UV.embed g)))
    embeddedProduct =
      BishopP.≃-trans
        (Embed.embedMul u (g * g))
        (BishopP.*-cong BishopP.≃-refl (Embed.embedMul g g))
  in
  BishopP.≃-trans
    (BishopP.≃-symm embeddedProduct)
    (subst
      (λ selected →
        Bishop._≃_ (UV.embed selected) Bishop.1ℝ)
      (sym sourceLaw)
      Embed.embedOne)

record P3InitialInverseSquareUsesHistoryCoupling
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    {Mode Atom : Set}
    {betaData}
    (history : History.FiniteModeInverseSquareTerminalHistoryData
      trajectory Mode Atom betaData)
    (running : SU2.CanonicalBishopSU2RunningInputs Nat) : Set₁ where
  field
    p3InitialInverseCancelsSameCouplingSquare :
      Bishop._≃_
        (Bishop._*_
          (P3.inverseCouplingSq (SU2.recursion running) zero)
          (square (UV.embed (History.couplingAt history zero))))
        Bishop.1ℝ

open P3InitialInverseSquareUsesHistoryCoupling public

p3InitialInverseCouplingSameSource :
  ∀ {trajectory Mode Atom betaData history running} →
  P3InitialInverseSquareUsesHistoryCoupling
    {trajectory = trajectory} {Mode = Mode} {Atom = Atom} {betaData = betaData}
    history running →
  Bishop._≃_
    (P3.inverseCouplingSq (SU2.recursion running) zero)
    (UV.embed (Flow.inverseCoupling trajectory zero))
p3InitialInverseCouplingSameSource
    {trajectory = trajectory} {history = history} {running = running}
    sameCoupling =
  let
    g = UV.embed (History.couplingAt history zero)
    gPositive = embeddedCouplingPositive
      (History.couplingAt history zero)
      (History.couplingPositive history zero)
    squarePositive = Inverse.productPositive gPositive gPositive
    squareNonzero = Inverse.productNonzero gPositive gPositive

    p3Candidate = P3.inverseCouplingSq (SU2.recursion running) zero
    sourceCandidate = UV.embed (Flow.inverseCoupling trajectory zero)

    canonicalToP3 =
      Inverse.inverseFromCancellation
        (square g) p3Candidate squareNonzero
        (p3InitialInverseCancelsSameCouplingSquare sameCoupling)

    canonicalToSource =
      Inverse.inverseFromCancellation
        (square g) sourceCandidate squareNonzero
        (embeddedSourceInverseCancelsCouplingSquare history)
  in
  BishopP.≃-trans
    (BishopP.≃-symm canonicalToP3)
    canonicalToSource

directUVAnchorWitnessRequired : Agda.Builtin.Bool.Bool
directUVAnchorWitnessRequired = Agda.Builtin.Bool.false

sharedInitialCouplingInverseSquareRepresentationRequired : Agda.Builtin.Bool.Bool
sharedInitialCouplingInverseSquareRepresentationRequired = Agda.Builtin.Bool.true

p3UVAnchorFromSharedCouplingCompilerLevel : ProofLevel
p3UVAnchorFromSharedCouplingCompilerLevel = machineChecked

p3InitialInverseSquareRepresentationLevel : ProofLevel
p3InitialInverseSquareRepresentationLevel = conditional
