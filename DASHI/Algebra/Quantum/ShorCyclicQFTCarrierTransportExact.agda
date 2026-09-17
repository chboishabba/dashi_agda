module DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Analysis.NonArchimedeanLocalDFTParsevalSourceExact as DFTSource

------------------------------------------------------------------------
-- SHOR CYCLIC-QFT CARRIER TRANSPORT
--
-- Existing source authority reused here (not re-proved):
--
--   sneed-and-feed/adelic-spectral-zeta
--   formalization/Formalization/Analysis/DFT.lean
--   repository commit 0c3e98c144796f99534f372b4aba977e6b76ee19
--
-- That source uses the normalized `dftMatrix` on finite cyclic `ZMod N` and
-- the underlying Mathlib-upstream DFT theorems `dft_mul_star` and
-- `dft_star_mul`.  DASHI already records the corresponding source receipt in
-- `NonArchimedeanLocalDFTParsevalSourceExact`.
--
-- External repository licence at the pinned source revision: CC BY 4.0.
-- This file is a DASHI transport theorem.  It does not copy the Lean proof and
-- does not claim that Agda kernel-checks the external complex-matrix theorem.
--
-- Q2 is therefore split correctly:
--
--   source cyclic DFT inversion                     [existing source authority]
--   exact source-state <-> Shor-register weld      [explicit input here]
--   transported FiniteFourierTransform             [proved below]
--
-- The only mathematical content added here is transport of a two-sided inverse
-- through an exact carrier equivalence.
------------------------------------------------------------------------

record ShorCyclicQFTSourceReceipt : Set where
  constructor shorCyclicQFTSourceReceipt
  field
    sourceRepository : String
    sourceRevision : String
    sourceFile : String
    forwardInverseTheorem : String
    inverseForwardTheorem : String
    sourceLicence : String
    sourceIsExternalLean : Bool
    agdaKernelChecksSourceTheorem : Bool

open ShorCyclicQFTSourceReceipt public

canonicalShorCyclicQFTSourceReceipt : ShorCyclicQFTSourceReceipt
canonicalShorCyclicQFTSourceReceipt =
  shorCyclicQFTSourceReceipt
    "sneed-and-feed/adelic-spectral-zeta"
    "0c3e98c144796f99534f372b4aba977e6b76ee19"
    "formalization/Formalization/Analysis/DFT.lean"
    "MathlibUpstream.Analysis.DFT.dft_mul_star"
    "MathlibUpstream.Analysis.DFT.dft_star_mul"
    "CC BY 4.0"
    true
    false

record CyclicDFTAction (SourceState : Set) : Set₁ where
  constructor cyclicDFTAction
  field
    sourceForward : SourceState → SourceState
    sourceInverse : SourceState → SourceState
    sourceInverseAfterForward :
      ∀ ψ → sourceInverse (sourceForward ψ) ≡ ψ
    sourceForwardAfterInverse :
      ∀ ψ → sourceForward (sourceInverse ψ) ≡ ψ

open CyclicDFTAction public

record CyclicQFTCarrierWeld
    {B : Finite.FiniteBasis}
    (R : Finite.FiniteQuantumRegister B)
    {SourceState : Set}
    (source : CyclicDFTAction SourceState) : Set₁ where
  constructor cyclicQFTCarrierWeld
  field
    toRegister : SourceState → Finite.State R
    fromRegister : Finite.State R → SourceState

    fromToRegister :
      ∀ ψ → fromRegister (toRegister ψ) ≡ ψ

    toFromRegister :
      ∀ ψ → toRegister (fromRegister ψ) ≡ ψ

open CyclicQFTCarrierWeld public

transportCyclicDFTToFiniteQFT :
  ∀ {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {source : CyclicDFTAction SourceState} →
  CyclicQFTCarrierWeld R source →
  QFT.FiniteFourierTransform R
transportCyclicDFTToFiniteQFT {source = source} W = record
  { fourier =
      λ ψ →
        toRegister W
          (sourceForward source (fromRegister W ψ))
  ; inverseFourier =
      λ ψ →
        toRegister W
          (sourceInverse source (fromRegister W ψ))
  ; inverseAfterFourier = inverseAfter
  ; fourierAfterInverse = forwardAfter
  }
  where
    inverseAfter :
      ∀ ψ →
      toRegister W
        (sourceInverse source
          (fromRegister W
            (toRegister W
              (sourceForward source (fromRegister W ψ)))))
      ≡ ψ
    inverseAfter ψ
      rewrite fromToRegister W
        (sourceForward source (fromRegister W ψ))
            | sourceInverseAfterForward source (fromRegister W ψ)
      = toFromRegister W ψ

    forwardAfter :
      ∀ ψ →
      toRegister W
        (sourceForward source
          (fromRegister W
            (toRegister W
              (sourceInverse source (fromRegister W ψ)))))
      ≡ ψ
    forwardAfter ψ
      rewrite fromToRegister W
        (sourceInverse source (fromRegister W ψ))
            | sourceForwardAfterInverse source (fromRegister W ψ)
      = toFromRegister W ψ

transportedForwardExact :
  ∀ {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {source : CyclicDFTAction SourceState} →
  (W : CyclicQFTCarrierWeld R source) →
  (ψ : Finite.State R) →
  QFT.fourier (transportCyclicDFTToFiniteQFT W) ψ
  ≡
  toRegister W (sourceForward source (fromRegister W ψ))
transportedForwardExact W ψ = refl

transportedInverseExact :
  ∀ {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {source : CyclicDFTAction SourceState} →
  (W : CyclicQFTCarrierWeld R source) →
  (ψ : Finite.State R) →
  QFT.inverseFourier (transportCyclicDFTToFiniteQFT W) ψ
  ≡
  toRegister W (sourceInverse source (fromRegister W ψ))
transportedInverseExact W ψ = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record ShorCyclicQFTTransportBoundary : Set where
  constructor shorCyclicQFTTransportBoundary
  field
    normalizedCyclicDFTSourceOwned : Bool
    sourceTwoSidedInverseOwned : Bool
    sourceAttributionPinned : Bool
    transportCompilerClosed : Bool
    sourceRegisterSameObjectSuppliedByThisModule : Bool
    samplingDistributionSuppliedByThisModule : Bool
    continuedFractionRecoverySuppliedByThisModule : Bool
    physicalQFTCircuitClaimed : Bool

canonicalShorCyclicQFTTransportBoundary : ShorCyclicQFTTransportBoundary
canonicalShorCyclicQFTTransportBoundary =
  shorCyclicQFTTransportBoundary
    true true true true false false false false

sourceDFTUnitarityReceiptRetained :
  DFTSource.LocalDFTParsevalSourceReceipt.localDFTIsUnitary
    DFTSource.canonicalLocalDFTParsevalSourceReceipt
  ≡ true
sourceDFTUnitarityReceiptRetained =
  DFTSource.localDFTUnitaryOwned
