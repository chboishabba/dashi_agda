{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650Rational345RelaxedEnvelopeRound855Exact where

------------------------------------------------------------------------
-- NS R855. EXACT SAME ORIGINAL R829 3-4-5 rate and R830 horizon.
--
-- A source derivative bound TEN MILLION TIMES L_R828 still implies
-- r(t)<0 throughout the original R854 short interval.
-- A bound TWENTY MILLION TIMES L_R828 still implies NEGATIVE INTEGRAL
-- of the affine envelope over that same fixed interval.
--
-- These are unconditional rational implications, not a proof that
-- the actual original R853 rate obeys either relaxed derivative bound.
-- The real Galerkin trajectory and R853 identification remain OPEN.
-- SOURCE-WRITTEN; pinned Agda 2.9 kernel execution pending.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _/_; _+_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNR650Rational345LipschitzIntegralRound854Exact as R854

weakPointwiseFactor855 : ℚ
weakPointwiseFactor855 = (+ 10000000) / 1

weakIntegratedFactor855 : ℚ
weakIntegratedFactor855 = (+ 20000000) / 1

weakPointwiseLipschitzBudget855 : ℚ
weakPointwiseLipschitzBudget855 =
  weakPointwiseFactor855 * R854.sourceLipschitzConstant854

weakIntegratedLipschitzBudget855 : ℚ
weakIntegratedLipschitzBudget855 =
  weakIntegratedFactor855 * R854.sourceLipschitzConstant854

weakPointwiseTerminalUpper855 : ℚ
weakPointwiseTerminalUpper855 =
  R854.actualInitialSelectedRate854
  + weakPointwiseLipschitzBudget855 * R854.exactHorizon854

weakPointwiseTerminalNegative855 :
  weakPointwiseTerminalUpper855 < 0ℚ
weakPointwiseTerminalNegative855 =
  toWitness (ℚP._<?_ weakPointwiseTerminalUpper855 0ℚ)

weakIntegratedAffineUpper855 : ℚ
weakIntegratedAffineUpper855 =
  R854.actualInitialSelectedRate854 * R854.exactHorizon854
  + ((weakIntegratedLipschitzBudget855 *
       R854.exactHorizon854 * R854.exactHorizon854) / 2)

weakIntegratedAffineNegative855 :
  weakIntegratedAffineUpper855 < 0ℚ
weakIntegratedAffineNegative855 =
  toWitness (ℚP._<?_ weakIntegratedAffineUpper855 0ℚ)

-- Source-specific remaining obligations:
-- originalR71RealGalerkinLocalSolution
-- originalR853SignedRateAlongGalerkinSolution
-- originalR853RateDerivativeBoundAtMostWeakBudget855
-- originalR855ActualSourceRateEnvelope
-- The last two consume the original R853 field, NOT free scalars.
