{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowAWardFloorCanonicalGateExact where

------------------------------------------------------------------------
-- ROW A: EXPLICIT WARD-PATCH GAUSSIAN FLOOR -> CANONICAL CAUCHY GATE
--
-- Cross-prover calibration from the current Lean lane gives the Gaussian
-- two-sided shell lower bound
--
--                     beta_Z >= 1 / 8388608.
--
-- This module treats only the exact rational arithmetic of that value.  It does
-- NOT claim the remaining same-object identification with CMP109/CMP99.
--
-- The local normalized-interaction Cauchy package supplies C and L_local.  The
-- full generated trajectory may additionally carry a propagated/history
-- sensitivity L_history.  Given that one nonnegative history constant, the
-- canonical cap is a definition:
--
--   gamma* = b_Ward / (2 (C + L_local + L_history + 1)).
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _/_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Nullary.Decidable using (toWitness)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact as Cauchy

wardGaussianFloor : ℚ
wardGaussianFloor = + 1 / 8388608

wardGaussianFloorPositive : 0ℚ < wardGaussianFloor
wardGaussianFloorPositive =
  toWitness {a? = 0ℚ ℚP.<? wardGaussianFloor} _

wardCauchySourceConstants :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (historyConstant : ℚ) →
  0ℚ ≤ historyConstant →
  Cauchy.RowACauchySourceConstants
wardCauchySourceConstants mixed historyConstant historyNN = record
  { Cauchy.RowACauchySourceConstants.gaussianFloor = wardGaussianFloor
  ; Cauchy.RowACauchySourceConstants.gaussianFloorPositive =
      wardGaussianFloorPositive
  ; Cauchy.RowACauchySourceConstants.mixedInteraction = mixed
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstant = historyConstant
  ; Cauchy.RowACauchySourceConstants.historyDerivativeConstantNonnegative = historyNN
  }

wardCanonicalGamma :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (historyConstant : ℚ) →
  0ℚ ≤ historyConstant → ℚ
wardCanonicalGamma mixed historyConstant historyNN =
  Cauchy.canonicalSourceGamma
    (wardCauchySourceConstants mixed historyConstant historyNN)

wardCanonicalGammaPositive :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (historyConstant : ℚ) →
  (historyNN : 0ℚ ≤ historyConstant) →
  0ℚ < wardCanonicalGamma mixed historyConstant historyNN
wardCanonicalGammaPositive mixed historyConstant historyNN =
  Cauchy.canonicalSourceGammaPositive
    (wardCauchySourceConstants mixed historyConstant historyNN)

wardCanonicalGammaPaysCombinedGate :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (historyConstant : ℚ) →
  (historyNN : 0ℚ ≤ historyConstant) →
  let source = wardCauchySourceConstants mixed historyConstant historyNN
  in
  (Cauchy.sourceInteractionConstant source
    + Cauchy.sourceDerivativeConstant source)
    * wardCanonicalGamma mixed historyConstant historyNN
  < wardGaussianFloor
wardCanonicalGammaPaysCombinedGate mixed historyConstant historyNN =
  Cauchy.canonicalSourceGammaPaysCombinedGate
    (wardCauchySourceConstants mixed historyConstant historyNN)

wardGaussianFloorArithmeticLevel : ProofLevel
wardGaussianFloorArithmeticLevel = machineChecked

wardFloorToCanonicalSmallCouplingLevel : ProofLevel
wardFloorToCanonicalSmallCouplingLevel = machineChecked

-- Physical/source seams: identify the literal Gaussian contribution with the
-- Ward-transverse patch, instantiate the local mixed-Cauchy package, and derive
-- the finite propagated/history response on the same generated trajectory.
literalCMP109WardGaussianFloorIdentificationLevel : ProofLevel
literalCMP109WardGaussianFloorIdentificationLevel = conditional

literalCMP109MixedInteractionCauchyInstantiationLevel : ProofLevel
literalCMP109MixedInteractionCauchyInstantiationLevel = conditional

literalCMP109HistorySensitivityInstantiationLevel : ProofLevel
literalCMP109HistorySensitivityInstantiationLevel = conditional
