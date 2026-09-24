module DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportRegression where

open import DASHI.Core.Prelude

import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Transport

------------------------------------------------------------------------
-- RED regression: once an exact source/register carrier weld is supplied,
-- the already-certified cyclic DFT action must compile to the existing finite
-- QFT interface without reproving Fourier inversion.
------------------------------------------------------------------------

transportedQFTExists :
  ∀ {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {source : Transport.CyclicDFTAction SourceState} →
  Transport.CyclicQFTCarrierWeld R source →
  QFT.FiniteFourierTransform R
transportedQFTExists = Transport.transportCyclicDFTToFiniteQFT

transportedForwardIsSourceForward :
  ∀ {B : Finite.FiniteBasis}
    {R : Finite.FiniteQuantumRegister B}
    {SourceState : Set}
    {source : Transport.CyclicDFTAction SourceState} →
  (W : Transport.CyclicQFTCarrierWeld R source) →
  (ψ : Finite.State R) →
  QFT.fourier (Transport.transportCyclicDFTToFiniteQFT W) ψ
  ≡
  Transport.toRegister W
    (Transport.sourceForward source (Transport.fromRegister W ψ))
transportedForwardIsSourceForward W ψ = refl
