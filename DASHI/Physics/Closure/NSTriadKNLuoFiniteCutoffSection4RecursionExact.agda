module DASHI.Physics.Closure.NSTriadKNLuoFiniteCutoffSection4RecursionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- PURPOSE
-- Compose the concrete finite terminal cutoff inequality with the four
-- Section-4 interaction sums and the exact finite Schur bound.  The boundary
-- energy is moved to the right by an ordered-field proof, yielding
--
--   E_out + D
--     <= E_boundary + (512/93) G W.
--
-- This is the finite cutoff-to-recursion calculation itself; no final
-- recursion inequality is accepted as a field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNLuoFiniteFourInteractionSchurBoundsExact as Four

moveCutoffBoundary :
  ∀ outputEnergy boundaryEnergy dissipation flux majorant →
  outputEnergy - boundaryEnergy + dissipation ≤ flux →
  flux ≤ majorant →
  outputEnergy + dissipation ≤ boundaryEnergy + majorant
moveCutoffBoundary
  outputEnergy boundaryEnergy dissipation flux majorant
  terminalEstimate fluxBound =
  let
    cutoffToMajorant :
      outputEnergy - boundaryEnergy + dissipation ≤ majorant
    cutoffToMajorant =
      ℚₚ.≤-trans terminalEstimate fluxBound

    addBoundary :
      boundaryEnergy + (outputEnergy - boundaryEnergy + dissipation)
      ≤ boundaryEnergy + majorant
    addBoundary =
      ℚₚ.+-mono-≤ ℚₚ.≤-refl cutoffToMajorant

    cancelBoundary :
      boundaryEnergy + (outputEnergy - boundaryEnergy + dissipation)
      ≡ outputEnergy + dissipation
    cancelBoundary =
      solve
        (outputEnergy ∷ boundaryEnergy ∷ dissipation ∷ [])
  in
  subst
    (λ left → left ≤ boundaryEnergy + majorant)
    cancelBoundary
    addBoundary

record FiniteCutoffSection4Data : Set where
  constructor finite-cutoff-section4
  field
    interactions : Four.FiniteFourInteractionData
    lowCutoff gapCutoff : Nat

    outputEnergy boundaryEnergy dissipation physicalFlux : ℚ

    terminalCutoffEstimate :
      outputEnergy - boundaryEnergy + dissipation
      ≤ physicalFlux

    physicalFluxBelowSection4Total :
      physicalFlux
      ≤ Four.section4TotalMagnitude
          interactions lowCutoff gapCutoff

open FiniteCutoffSection4Data public

finitePhysicalFluxBelowSchurMajorant :
  (data : FiniteCutoffSection4Data) →
  physicalFlux data
  ≤ Four.section4AggregateConstant
      * Four.section4CommonFactor (interactions data)
finitePhysicalFluxBelowSchurMajorant data =
  ℚₚ.≤-trans
    (physicalFluxBelowSection4Total data)
    (Four.section4TotalFiniteBound
      (interactions data)
      (lowCutoff data)
      (gapCutoff data))

finiteCutoffSection4Recursion :
  (data : FiniteCutoffSection4Data) →
  outputEnergy data + dissipation data
  ≤ boundaryEnergy data
      + Four.section4AggregateConstant
          * Four.section4CommonFactor (interactions data)
finiteCutoffSection4Recursion data =
  moveCutoffBoundary
    (outputEnergy data)
    (boundaryEnergy data)
    (dissipation data)
    (physicalFlux data)
    (Four.section4AggregateConstant
      * Four.section4CommonFactor (interactions data))
    (terminalCutoffEstimate data)
    (finitePhysicalFluxBelowSchurMajorant data)

finiteCutoffSection4CompositionClosed : Bool
finiteCutoffSection4CompositionClosed = true

finiteBoundaryCancellationClosed : Bool
finiteBoundaryCancellationClosed = true

finiteCutoffSection4CompositionClosedIsTrue :
  finiteCutoffSection4CompositionClosed ≡ true
finiteCutoffSection4CompositionClosedIsTrue = refl

finiteBoundaryCancellationClosedIsTrue :
  finiteBoundaryCancellationClosed ≡ true
finiteBoundaryCancellationClosedIsTrue = refl
