{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEventualFiniteSignFromVanishingErrorExact where

open import Data.Nat.Base using (ℕ; _≤_)
open import Data.Product.Base using (Σ; proj₁; proj₂)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _<ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Foundations.CMP119AntigravityFiniteToLocalCAnomalyLimitTransportExact as Transport
import DASHI.Physics.Foundations.CMP119AntigravityFiniteCutoffSignFromContinuumMarginExact as Sign
import DASHI.Physics.Foundations.CMP119AntigravityPinnedLocalCTraceAnomalyBridgeExact as LocalC
import DASHI.Physics.Foundations.CMP119AntigravityRealSU2TraceClosureExact as SU2Trace
import DASHI.Physics.YangMills.YangMillsContinuumLocalOperatorOPEStressTensorExact as Local
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq

------------------------------------------------------------------------
-- VANISHING ERROR -> EVENTUAL STRICT SIGN
--
-- The generic sequence-limit owner deliberately keeps Vanishes abstract.
-- For strict finite-cutoff sign transport we need only its ordinary epsilon
-- consequence: every positive tolerance eventually bounds the vanishing
-- sequence.
------------------------------------------------------------------------

record VanishingEventuallyBelow
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₁ where
  field
    eventuallyBelowPositive :
      ∀ error →
      Seq.Vanishes sequenceLimit error →
      ∀ tolerance →
      0ℝ <ℝ tolerance →
      Σ ℕ (λ threshold →
        ∀ cutoff → threshold ≤ cutoff →
        error cutoff <ℝ tolerance)

open VanishingEventuallyBelow public

vanishingEventuallyBelowLevel : ProofLevel
vanishingEventuallyBelowLevel = standardImported

record NonzeroTraceF2Margins
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    (readout :
      LocalC.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention) : Set₁ where
  field
    continuumTraceNegative :
      LocalC.stressTraceNumerator readout
        (Local.stressTensor localC)
      <ℝ 0ℝ

    continuumF2Positive :
      0ℝ <ℝ
      LocalC.localOperatorNumerator readout
        (Local.localOperator localC
          (LocalC.fieldStrengthSquarePolynomial readout))

    absNegativePositive :
      ∀ value → value <ℝ 0ℝ → 0ℝ <ℝ absℝ value

    absPositivePositive :
      ∀ value → 0ℝ <ℝ value → 0ℝ <ℝ absℝ value

open NonzeroTraceF2Margins public

record EventualFiniteAnomalySigns
    {ContinuumFamily CurvaturePolynomial LocalOperator Position
     OPECoefficient StressTensor Hamiltonian : Set}
    {localC :
      Local.ContinuumLocalOperatorOPEStressTensor
        ContinuumFamily CurvaturePolynomial LocalOperator Position
        OPECoefficient StressTensor Hamiltonian}
    {embedding : Embed.OrderedRationalRealEmbedding}
    {convention : SU2Trace.RealSU2TraceConvention embedding}
    {sequenceLimit : Seq.RealSequenceLimitByVanishingError}
    {readout :
      LocalC.SameFamilyLocalCTraceAnomalyReadout
        localC embedding convention}
    (transport :
      Transport.FiniteCMP119ToLocalCAnomalyLimitTransport
        sequenceLimit readout) : Set where
  field
    traceThreshold : ℕ
    f2Threshold : ℕ

    traceNegativeEventually :
      ∀ cutoff → traceThreshold ≤ cutoff →
      Transport.finiteQuantumTraceNumerator transport cutoff <ℝ 0ℝ

    f2PositiveEventually :
      ∀ cutoff → f2Threshold ≤ cutoff →
      0ℝ <ℝ Transport.finiteF2Numerator transport cutoff

open EventualFiniteAnomalySigns public

compileEventualFiniteAnomalySigns :
  ∀ {ContinuumFamily CurvaturePolynomial LocalOperator Position
      OPECoefficient StressTensor Hamiltonian localC embedding convention
      sequenceLimit readout}
    (vanishingSemantics : VanishingEventuallyBelow sequenceLimit)
    (stability : Sign.RealApproximationSignStability)
    (transport :
      Transport.FiniteCMP119ToLocalCAnomalyLimitTransport
        {ContinuumFamily = ContinuumFamily}
        {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator}
        {Position = Position}
        {OPECoefficient = OPECoefficient}
        {StressTensor = StressTensor}
        {Hamiltonian = Hamiltonian}
        {localC = localC}
        {embedding = embedding}
        {convention = convention}
        sequenceLimit readout)
    (margins : NonzeroTraceF2Margins readout) →
  EventualFiniteAnomalySigns transport
compileEventualFiniteAnomalySigns
    {localC = localC} {readout = readout}
    {sequenceLimit = sequenceLimit}
    vanishingSemantics stability transport margins =
  let
    traceTarget =
      LocalC.stressTraceNumerator readout
        (Local.stressTensor localC)

    f2Target =
      LocalC.localOperatorNumerator readout
        (Local.localOperator localC
          (LocalC.fieldStrengthSquarePolynomial readout))

    traceSmall =
      eventuallyBelowPositive vanishingSemantics
        (Transport.traceError transport)
        (Transport.traceErrorVanishes transport)
        (absℝ traceTarget)
        (absNegativePositive margins traceTarget
          (continuumTraceNegative margins))

    f2Small =
      eventuallyBelowPositive vanishingSemantics
        (Transport.f2Error transport)
        (Transport.f2ErrorVanishes transport)
        (absℝ f2Target)
        (absPositivePositive margins f2Target
          (continuumF2Positive margins))
  in record
    { EventualFiniteAnomalySigns.traceThreshold =
        proj₁ traceSmall
    ; EventualFiniteAnomalySigns.f2Threshold =
        proj₁ f2Small
    ; EventualFiniteAnomalySigns.traceNegativeEventually =
        λ cutoff hCutoff →
          Sign.negativeStable stability
            traceTarget
            (Transport.finiteQuantumTraceNumerator transport cutoff)
            (Transport.traceError transport cutoff)
            (continuumTraceNegative margins)
            (Transport.finiteTraceApproximatesLocalC transport cutoff)
            (proj₂ traceSmall cutoff hCutoff)
    ; EventualFiniteAnomalySigns.f2PositiveEventually =
        λ cutoff hCutoff →
          Sign.positiveStable stability
            f2Target
            (Transport.finiteF2Numerator transport cutoff)
            (Transport.f2Error transport cutoff)
            (continuumF2Positive margins)
            (Transport.finiteF2ApproximatesLocalC transport cutoff)
            (proj₂ f2Small cutoff hCutoff)
    }

eventualFiniteSignCompilerLevel : ProofLevel
eventualFiniteSignCompilerLevel = machineChecked
