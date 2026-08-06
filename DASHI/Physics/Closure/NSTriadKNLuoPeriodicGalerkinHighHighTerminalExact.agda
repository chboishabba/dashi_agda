module DASHI.Physics.Closure.NSTriadKNLuoPeriodicGalerkinHighHighTerminalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Title: finite Cauchy--Schwarz inequality.
-- DOI: not applicable to the nineteenth-century result.
--
-- PURPOSE
-- Wire the now-concrete finite periodic HH coefficient producer into the
-- terminal-window Cauchy theorem.  The caller no longer supplies an unrelated
-- critical-mass estimate: terminal left mass is identified with the actual
-- periodic H^{-1} producer, and its bound is derived from the closed Leray,
-- support-count, Fourier-coefficient and tensor-Holder chain.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.List.Base using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoFiniteHighHighTerminalCauchyExact as Terminal
import DASHI.Physics.Closure.NSTriadKNLuoRound14FinitePeriodicHighHighTensorClosedExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoRound14FinitePeriodicHighHighClosedExact as HHBase
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicBernsteinRealizationExact as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor

record PeriodicGalerkinHighHighTerminalData (Slot : Set) : Set₁ where
  constructor periodic-galerkin-high-high-terminal-data
  field
    periodicTensorData : HH.FinitePeriodicHighHighTensorData Slot
    terminalPairs : List L2.Pair

    interactionSquared criticalEnvelopeSquared outputEnvelopeSquared : ℚ

    interactionMeaning :
      interactionSquared ≡ L2.square (L2.pairDot terminalPairs)

    terminalLeftProducerMeaning :
      L2.leftNormSquared terminalPairs
      ≡ HHBase.finiteHMinusOneSquared
          (HH.periodicData periodicTensorData)

    producerEnvelopeBound :
      Bernstein.outputScaleCubed
          (HHBase.bernsteinData (HH.periodicData periodicTensorData))
        * (Tensor.leftL2Squared (HH.tensorData periodicTensorData)
          * Tensor.rightL2Squared (HH.tensorData periodicTensorData))
      ≤ criticalEnvelopeSquared

    criticalEnvelopeNonnegative : 0ℚ ≤ criticalEnvelopeSquared
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs ≤ outputEnvelopeSquared

open PeriodicGalerkinHighHighTerminalData public

periodicProducerCriticalBound :
  ∀ {Slot : Set}
    (dataSet : PeriodicGalerkinHighHighTerminalData Slot) →
  L2.leftNormSquared (terminalPairs dataSet)
  ≤ criticalEnvelopeSquared dataSet
periodicProducerCriticalBound dataSet =
  let
    producerBound :
      HHBase.finiteHMinusOneSquared
        (HH.periodicData (periodicTensorData dataSet))
      ≤ Bernstein.outputScaleCubed
          (HHBase.bernsteinData
            (HH.periodicData (periodicTensorData dataSet)))
        * (Tensor.leftL2Squared
            (HH.tensorData (periodicTensorData dataSet))
          * Tensor.rightL2Squared
            (HH.tensorData (periodicTensorData dataSet)))
    producerBound =
      HH.finitePeriodicHighHighTensorSquareBound
        (periodicTensorData dataSet)

    producerToEnvelope :
      HHBase.finiteHMinusOneSquared
        (HH.periodicData (periodicTensorData dataSet))
      ≤ criticalEnvelopeSquared dataSet
    producerToEnvelope =
      ℚₚ.≤-trans producerBound (producerEnvelopeBound dataSet)
  in
  subst
    (λ lower → lower ≤ criticalEnvelopeSquared dataSet)
    (sym (terminalLeftProducerMeaning dataSet))
    producerToEnvelope

periodicGalerkinHighHighTerminalSquareBound :
  ∀ {Slot : Set}
    (dataSet : PeriodicGalerkinHighHighTerminalData Slot) →
  interactionSquared dataSet
  ≤ criticalEnvelopeSquared dataSet
    * outputEnvelopeSquared dataSet
periodicGalerkinHighHighTerminalSquareBound dataSet =
  Terminal.finiteHighHighTerminalSquareBound
    (Terminal.high-high-terminal-cauchy-data
      (terminalPairs dataSet)
      (interactionSquared dataSet)
      (criticalEnvelopeSquared dataSet)
      (outputEnvelopeSquared dataSet)
      (interactionMeaning dataSet)
      (criticalEnvelopeNonnegative dataSet)
      (outputEnvelopeNonnegative dataSet)
      (periodicProducerCriticalBound dataSet)
      (outputMassBound dataSet))
