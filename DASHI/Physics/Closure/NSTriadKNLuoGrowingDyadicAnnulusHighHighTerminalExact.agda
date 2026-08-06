module DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusHighHighTerminalExact where

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
-- Carry the explicit annular/Galerkin high-high producer through the terminal
-- pairing.  The terminal left mass is identified with
--
--   ||Delta_q P div(u_p tensor u_p')||_(H^-1)^2,
--
-- already bounded by
--
--   125 * 8^q * ||u_p||_2^2 ||u_p'||_2^2.
--
-- Finite Cauchy--Schwarz then gives the classwise terminal square estimate
-- needed by the four-class assembly.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoGrowingDyadicAnnulusHighHighExact as HH
import DASHI.Physics.Closure.NSTriadKNLuoGrowingCubeHighHighTensorClosedExact as HHTensor
import DASHI.Physics.Closure.NSTriadKNLuoFiniteTensorHolderExact as Tensor
import DASHI.Physics.Closure.NSTriadKNLuoIntegerCubeSupportCapacityExact as Capacity

record AnnularHighHighTerminalData (shell : Nat) : Set₁ where
  constructor annular-high-high-terminal-data
  field
    highHighTensorData : HH.AnnularHighHighTensorData shell
    terminalPairs : List L2.Pair

    criticalEnvelopeSquared outputEnvelopeSquared : ℚ
    criticalEnvelopeNonnegative : 0ℚ ≤ criticalEnvelopeSquared
    outputEnvelopeNonnegative : 0ℚ ≤ outputEnvelopeSquared

    terminalLeftMeaning :
      L2.leftNormSquared terminalPairs
      ≡ HH.annularHighHighHMinusOneSquared
          shell
          (HH.annularHighHighData highHighTensorData)

    producerEnvelopeBound :
      (Capacity.oneTwentyFive * Capacity.eightPower shell)
        * (Tensor.leftL2Squared (HH.tensorData highHighTensorData)
          * Tensor.rightL2Squared (HH.tensorData highHighTensorData))
      ≤ criticalEnvelopeSquared

    outputMassBound :
      L2.rightNormSquared terminalPairs ≤ outputEnvelopeSquared

open AnnularHighHighTerminalData public

highHighInteraction :
  ∀ {shell : Nat} →
  AnnularHighHighTerminalData shell → ℚ
highHighInteraction dataSet = L2.pairDot (terminalPairs dataSet)

terminalLeftByCriticalEnvelope :
  ∀ {shell : Nat}
    (dataSet : AnnularHighHighTerminalData shell) →
  L2.leftNormSquared (terminalPairs dataSet)
  ≤ criticalEnvelopeSquared dataSet
terminalLeftByCriticalEnvelope {shell} dataSet =
  let
    producerBound =
      HH.annularHighHighTensorSquareBound
        shell
        (highHighTensorData dataSet)

    toEnvelope =
      ℚₚ.≤-trans producerBound (producerEnvelopeBound dataSet)
  in
  subst
    (λ lower → lower ≤ criticalEnvelopeSquared dataSet)
    (sym (terminalLeftMeaning dataSet))
    toEnvelope

annularHighHighTerminalSquareBound :
  ∀ {shell : Nat}
    (dataSet : AnnularHighHighTerminalData shell) →
  L2.square (highHighInteraction dataSet)
  ≤ criticalEnvelopeSquared dataSet
    * outputEnvelopeSquared dataSet
annularHighHighTerminalSquareBound dataSet =
  let
    cauchy = L2.finiteCauchySchwarzSquared (terminalPairs dataSet)

    envelopeProduct =
      L2.nonnegativeProductMonotone
        (L2.leftNormSquaredNonnegative (terminalPairs dataSet))
        (L2.rightNormSquaredNonnegative (terminalPairs dataSet))
        (criticalEnvelopeNonnegative dataSet)
        (outputEnvelopeNonnegative dataSet)
        (terminalLeftByCriticalEnvelope dataSet)
        (outputMassBound dataSet)
  in
  ℚₚ.≤-trans cauchy envelopeProduct
