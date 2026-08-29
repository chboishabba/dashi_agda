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
-- NOT claim the remaining same-object identification with CMP109/CMP99; that
-- identification stays explicit below.
--
-- Combining the fixed positive floor with the existing normalized-interaction
-- mixed-Cauchy package means the canonical small-coupling cap becomes a
-- definition of the source package alone:
--
--   gamma* = b_Ward / (2 (C + L + 1)).
--
-- Thus once the literal source interaction package and the Ward-patch
-- same-object theorem are supplied, no additional positive-floor variable or
-- small-coupling search remains.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _<_)
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
  Mixed.MixedInteractionCauchyData → Cauchy.RowACauchySourceConstants
wardCauchySourceConstants mixed = record
  { Cauchy.RowACauchySourceConstants.gaussianFloor = wardGaussianFloor
  ; Cauchy.RowACauchySourceConstants.gaussianFloorPositive =
      wardGaussianFloorPositive
  ; Cauchy.RowACauchySourceConstants.mixedInteraction = mixed
  }

wardCanonicalGamma : Mixed.MixedInteractionCauchyData → ℚ
wardCanonicalGamma mixed =
  Cauchy.canonicalSourceGamma (wardCauchySourceConstants mixed)

wardCanonicalGammaPositive :
  (mixed : Mixed.MixedInteractionCauchyData) →
  0ℚ < wardCanonicalGamma mixed
wardCanonicalGammaPositive mixed =
  Cauchy.canonicalSourceGammaPositive (wardCauchySourceConstants mixed)

wardCanonicalGammaPaysCombinedGate :
  (mixed : Mixed.MixedInteractionCauchyData) →
  (Cauchy.sourceInteractionConstant (wardCauchySourceConstants mixed)
    + Cauchy.sourceDerivativeConstant (wardCauchySourceConstants mixed))
    * wardCanonicalGamma mixed
  < wardGaussianFloor
wardCanonicalGammaPaysCombinedGate mixed =
  Cauchy.canonicalSourceGammaPaysCombinedGate (wardCauchySourceConstants mixed)

wardGaussianFloorArithmeticLevel : ProofLevel
wardGaussianFloorArithmeticLevel = machineChecked

wardFloorToCanonicalSmallCouplingLevel : ProofLevel
wardFloorToCanonicalSmallCouplingLevel = machineChecked

-- Physical/source seam: identify the exact Gaussian contribution in the
-- literal CMP109/CMP99 constrained shell with the Ward-transverse positive patch
-- carrying the displayed lower bound, and instantiate the normalized-interaction
-- mixed-Cauchy package on the SAME generated trajectory.
literalCMP109WardGaussianFloorIdentificationLevel : ProofLevel
literalCMP109WardGaussianFloorIdentificationLevel = conditional

literalCMP109MixedInteractionCauchyInstantiationLevel : ProofLevel
literalCMP109MixedInteractionCauchyInstantiationLevel = conditional
