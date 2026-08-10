module DASHI.Physics.Closure.NSTriadKNComCoarseFineNaturalityRound36Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier--Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Piero D'Ancona.
-- Title: "A Short Proof of Commutator Estimates".
-- DOI: 10.1007/s00041-018-9612-8.
-- Correction DOI: 10.1007/s00041-019-09724-7.
--
-- DASHI CONTRIBUTION
--
-- Make the "Com is failure of coarse graining to commute with transport"
-- interpretation literal on a finite exact carrier.
--
-- For a kernel projection
--
--   P f = sum_y K_y f_y
--
-- and scalar transport T_y f_y = u_y f_y, evaluated against output velocity
-- u_x, the finite commutator is
--
--   P(T f) - u_x P f
--     = sum_y K_y (u_y - u_x) f_y.
--
-- The right side is exactly the transport increment across one coarse fibre.
-- It vanishes for a velocity that is constant on the fibre.  This is the
-- algebraic real-space seam that the Round-35 Gram/Cotlar programme must turn
-- into the literal T_q^*T_r and T_qT_r^* operator estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record CenteredTransportSample : Set where
  constructor centered-transport-sample
  field
    kernelWeight : ℚ
    fibreVelocity : ℚ
    differentiatedSignal : ℚ

open CenteredTransportSample public

projectSignal : List CenteredTransportSample → ℚ
projectSignal [] = 0ℚ
projectSignal (sample ∷ rest) =
  kernelWeight sample * differentiatedSignal sample
  + projectSignal rest

projectTransport : List CenteredTransportSample → ℚ
projectTransport [] = 0ℚ
projectTransport (sample ∷ rest) =
  kernelWeight sample
    * (fibreVelocity sample * differentiatedSignal sample)
  + projectTransport rest

transportProjected : ℚ → List CenteredTransportSample → ℚ
transportProjected outputVelocity samples =
  outputVelocity * projectSignal samples

coarseFineNaturalityDefect :
  ℚ → List CenteredTransportSample → ℚ
coarseFineNaturalityDefect outputVelocity samples =
  projectTransport samples - transportProjected outputVelocity samples

incrementDefect : ℚ → List CenteredTransportSample → ℚ
incrementDefect outputVelocity [] = 0ℚ
incrementDefect outputVelocity (sample ∷ rest) =
  kernelWeight sample
    * ((fibreVelocity sample - outputVelocity)
      * differentiatedSignal sample)
  + incrementDefect outputVelocity rest

coarseFineNaturalityDefectIsIncrementSum :
  ∀ outputVelocity samples →
  coarseFineNaturalityDefect outputVelocity samples
  ≡ incrementDefect outputVelocity samples
coarseFineNaturalityDefectIsIncrementSum outputVelocity [] = solve []
coarseFineNaturalityDefectIsIncrementSum outputVelocity (sample ∷ rest) =
  trans
    (cong
      (λ tailDifference →
        kernelWeight sample
          * (fibreVelocity sample * differentiatedSignal sample)
        + projectTransport rest
        - outputVelocity
          * (kernelWeight sample * differentiatedSignal sample
            + projectSignal rest))
      refl)
    (trans
      (cong
        (λ tailDefect →
          kernelWeight sample
            * ((fibreVelocity sample - outputVelocity)
              * differentiatedSignal sample)
          + tailDefect)
        (coarseFineNaturalityDefectIsIncrementSum outputVelocity rest))
      (solve
        ( kernelWeight sample
        ∷ fibreVelocity sample
        ∷ differentiatedSignal sample
        ∷ outputVelocity
        ∷ projectTransport rest
        ∷ projectSignal rest
        ∷ []))))

constantVelocitySamples :
  ℚ → List CenteredTransportSample → List CenteredTransportSample
constantVelocitySamples outputVelocity [] = []
constantVelocitySamples outputVelocity (sample ∷ rest) =
  centered-transport-sample
    (kernelWeight sample)
    outputVelocity
    (differentiatedSignal sample)
  ∷ constantVelocitySamples outputVelocity rest

constantVelocityIncrementDefectZero :
  ∀ outputVelocity samples →
  incrementDefect outputVelocity (constantVelocitySamples outputVelocity samples)
  ≡ 0ℚ
constantVelocityIncrementDefectZero outputVelocity [] = refl
constantVelocityIncrementDefectZero outputVelocity (sample ∷ rest) =
  trans
    (cong
      (λ tail →
        kernelWeight sample
          * ((outputVelocity - outputVelocity)
            * differentiatedSignal sample)
        + tail)
      (constantVelocityIncrementDefectZero outputVelocity rest))
    (solve
      (kernelWeight sample
      ∷ outputVelocity
      ∷ differentiatedSignal sample
      ∷ []))

constantVelocityNaturalitySquareCommutes :
  ∀ outputVelocity samples →
  coarseFineNaturalityDefect
    outputVelocity (constantVelocitySamples outputVelocity samples)
  ≡ 0ℚ
constantVelocityNaturalitySquareCommutes outputVelocity samples =
  trans
    (coarseFineNaturalityDefectIsIncrementSum
      outputVelocity (constantVelocitySamples outputVelocity samples))
    (constantVelocityIncrementDefectZero outputVelocity samples)

comCoarseFineNaturalityIdentityClosed : Bool
comCoarseFineNaturalityIdentityClosed = true

literalComPairProductRealizationConstructed : Bool
literalComPairProductRealizationConstructed = false

comCoarseFineNaturalityIdentityClosedIsTrue :
  comCoarseFineNaturalityIdentityClosed ≡ true
comCoarseFineNaturalityIdentityClosedIsTrue = refl

literalComPairProductRealizationConstructedIsFalse :
  literalComPairProductRealizationConstructed ≡ false
literalComPairProductRealizationConstructedIsFalse = refl
