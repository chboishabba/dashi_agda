{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact where

------------------------------------------------------------------------
-- ROW A: ONE MIXED-CAUCHY SOURCE PACKAGE -> C, L -> CANONICAL SMALL COUPLING
--
-- Current master already proves, from one normalized interaction package,
--
--   |beta_int| <= C g
--
-- and from its mixed coupling derivative package,
--
--   |d_g beta_int| <= L.
--
-- Round95 already proves that any positive Gaussian floor b and finite
-- nonnegative C,L admit the explicit cap
--
--       gamma* = b / (2 (C + L + 1))
--
-- with (C+L) gamma* < b.  This file removes the remaining artificial seam
-- between those source-derived constants and the canonical Row-A gate.
--
-- The only physical data left in this carrier are therefore:
--   * the SAME literal mixed-Cauchy package for the normalized interaction;
--   * a literal positive Gaussian floor;
--   * the literal trajectory identifications/inequalities.
--
-- No independent existence assumptions for C, L, or sufficiently small gamma
-- remain after this conversion.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4InteractionLogHessianCauchyGateExact as H
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as Choice
import DASHI.Physics.YangMills.BalabanYM4RowACombinedGateCompositionExact as Combined

------------------------------------------------------------------------
-- Source constants are definitions of the already-proved Cauchy majorants.
------------------------------------------------------------------------

record RowACauchySourceConstants : Set where
  field
    gaussianFloor : ℚ
    gaussianFloorPositive : 0ℚ < gaussianFloor
    mixedInteraction : Mixed.MixedInteractionCauchyData

open RowACauchySourceConstants public

interactionData : RowACauchySourceConstants → H.InteractionCauchyData
interactionData source = Mixed.base (mixedInteraction source)

sourceInteractionConstant : RowACauchySourceConstants → ℚ
sourceInteractionConstant source = H.interactionConstant (interactionData source)

sourceDerivativeConstant : RowACauchySourceConstants → ℚ
sourceDerivativeConstant source = Mixed.interactionDerivativeConstant (mixedInteraction source)

sourceInteractionConstantNonnegative :
  (source : RowACauchySourceConstants) →
  0ℚ ≤ sourceInteractionConstant source
sourceInteractionConstantNonnegative source =
  let
    dataSet = interactionData source
    denominator = H.zLower dataSet * H.zLower dataSet
    denominatorPositive = H.zLowerSquaredPositive dataSet
    reciprocalNN = ℚP.<⇒≤
      (Quot.positiveReciprocalPositive denominator denominatorPositive)
  in
  H.mulNN (H.numeratorCoefficientNN dataSet) reciprocalNN

sourceDerivativeConstantNonnegative :
  (source : RowACauchySourceConstants) →
  0ℚ ≤ sourceDerivativeConstant source
sourceDerivativeConstantNonnegative source =
  let
    mixed = mixedInteraction source
    base = Mixed.base mixed
    denominator = (H.zLower base * H.zLower base) * H.zLower base
    denominatorPositive = Mixed.zLowerCubedPositive mixed
    reciprocalNN = ℚP.<⇒≤
      (Quot.positiveReciprocalPositive denominator denominatorPositive)
  in
  H.mulNN (Mixed.betaDerivativeNumeratorConstantNN mixed) reciprocalNN

asFiniteRowASourceConstants :
  RowACauchySourceConstants → Choice.FiniteRowASourceConstants
asFiniteRowASourceConstants source = record
  { Choice.FiniteRowASourceConstants.gaussianFloor = gaussianFloor source
  ; Choice.FiniteRowASourceConstants.interactionConstant =
      sourceInteractionConstant source
  ; Choice.FiniteRowASourceConstants.derivativeBound =
      sourceDerivativeConstant source
  ; Choice.FiniteRowASourceConstants.gaussianFloorPositive =
      gaussianFloorPositive source
  ; Choice.FiniteRowASourceConstants.interactionConstantNonnegative =
      sourceInteractionConstantNonnegative source
  ; Choice.FiniteRowASourceConstants.derivativeBoundNonnegative =
      sourceDerivativeConstantNonnegative source
  }

canonicalSourceGamma : RowACauchySourceConstants → ℚ
canonicalSourceGamma source =
  Choice.canonicalGamma (asFiniteRowASourceConstants source)

canonicalSourceGammaPositive :
  (source : RowACauchySourceConstants) → 0ℚ < canonicalSourceGamma source
canonicalSourceGammaPositive source =
  Choice.canonicalGammaPositive (asFiniteRowASourceConstants source)

canonicalSourceGammaPaysCombinedGate :
  (source : RowACauchySourceConstants) →
  (sourceInteractionConstant source + sourceDerivativeConstant source)
    * canonicalSourceGamma source
  < gaussianFloor source
canonicalSourceGammaPaysCombinedGate source =
  Choice.canonicalGammaPaysCombinedSmallness
    (asFiniteRowASourceConstants source)

------------------------------------------------------------------------
-- Literal trajectory carrier.  C,L,gamma are no longer fields.
------------------------------------------------------------------------

record CauchyCanonicalRowATrajectory (cutoff : Nat) : Set₁ where
  field
    source : RowACauchySourceConstants

    coupling betaGauss betaInteraction inverseSquare : Nat → ℚ
    tubeWidth : ℚ

    tubeWidthNonnegative : 0ℚ ≤ tubeWidth
    tubeWidthBelowCanonicalGamma :
      tubeWidth ≤ canonicalSourceGamma source

    couplingPositive : ∀ j → 0ℚ < coupling j
    couplingBelowCanonicalGamma : ∀ j →
      coupling j ≤ canonicalSourceGamma source

    gaussianLower : ∀ j →
      gaussianFloor source ≤ betaGauss j

    -- The interaction lower bound is exactly the coefficient produced by the
    -- normalized log-Hessian Cauchy package above.
    interactionLower : ∀ j →
      - (sourceInteractionConstant source * coupling j)
      ≤ betaInteraction j

    inverseSquareRelation : ∀ j →
      inverseSquare j * (coupling j * coupling j) ≡ (+ 1 / 1)

    couplingMonotone : ∀ j → coupling j ≤ coupling (suc j)

    betaIsInverseSquareStep : ∀ j → j ℕ.< cutoff →
      betaGauss j + betaInteraction j
      ≡ inverseSquare j - inverseSquare (suc j)

    couplingTube : ∀ K →
      coupling K - coupling 0 ≤ tubeWidth

open CauchyCanonicalRowATrajectory public

asCombinedRowAGateData :
  ∀ {cutoff} →
  CauchyCanonicalRowATrajectory cutoff →
  Combined.CombinedRowAGateData cutoff
asCombinedRowAGateData trajectory =
  let sourceData = source trajectory
  in record
    { Combined.CombinedRowAGateData.gaussianFloor = gaussianFloor sourceData
    ; Combined.CombinedRowAGateData.interactionConstant =
        sourceInteractionConstant sourceData
    ; Combined.CombinedRowAGateData.couplingCap =
        canonicalSourceGamma sourceData
    ; Combined.CombinedRowAGateData.tubeWidth = tubeWidth trajectory
    ; Combined.CombinedRowAGateData.derivativeBound =
        sourceDerivativeConstant sourceData
    ; Combined.CombinedRowAGateData.coupling = coupling trajectory
    ; Combined.CombinedRowAGateData.betaGauss = betaGauss trajectory
    ; Combined.CombinedRowAGateData.betaInteraction = betaInteraction trajectory
    ; Combined.CombinedRowAGateData.inverseSquare = inverseSquare trajectory
    ; Combined.CombinedRowAGateData.interactionConstantNN =
        sourceInteractionConstantNonnegative sourceData
    ; Combined.CombinedRowAGateData.derivativeBoundNN =
        sourceDerivativeConstantNonnegative sourceData
    ; Combined.CombinedRowAGateData.couplingCapNN =
        ℚP.<⇒≤ (canonicalSourceGammaPositive sourceData)
    ; Combined.CombinedRowAGateData.tubeWidthNN =
        tubeWidthNonnegative trajectory
    ; Combined.CombinedRowAGateData.tubeWidthBelowCouplingCap =
        tubeWidthBelowCanonicalGamma trajectory
    ; Combined.CombinedRowAGateData.couplingPositive =
        couplingPositive trajectory
    ; Combined.CombinedRowAGateData.couplingBelowCap =
        couplingBelowCanonicalGamma trajectory
    ; Combined.CombinedRowAGateData.gaussianLower = gaussianLower trajectory
    ; Combined.CombinedRowAGateData.interactionLower = interactionLower trajectory
    ; Combined.CombinedRowAGateData.inverseSquareRelation =
        inverseSquareRelation trajectory
    ; Combined.CombinedRowAGateData.couplingMonotone = couplingMonotone trajectory
    ; Combined.CombinedRowAGateData.betaIsInverseSquareStep =
        betaIsInverseSquareStep trajectory
    ; Combined.CombinedRowAGateData.couplingTube = couplingTube trajectory
    ; Combined.CombinedRowAGateData.combinedSmallness =
        canonicalSourceGammaPaysCombinedGate sourceData
    }

module CanonicalGate {cutoff : Nat}
    (trajectory : CauchyCanonicalRowATrajectory cutoff) where

  combined : Combined.CombinedRowAGateData cutoff
  combined = asCombinedRowAGateData trajectory

  open Combined.Combined combined public using
    (master; betaMargin; betaMarginPositive; inducedFlow; cubicSumBound; shootingGate)

------------------------------------------------------------------------
-- Authority boundary
------------------------------------------------------------------------

rowACauchyConstantsToCanonicalGammaLevel : ProofLevel
rowACauchyConstantsToCanonicalGammaLevel = machineChecked

rowACauchyCanonicalGateCompositionLevel : ProofLevel
rowACauchyCanonicalGateCompositionLevel = machineChecked

-- Remaining physical seam is now source-native: construct the literal
-- `MixedInteractionCauchyData` and the literal positive Gaussian floor on the
-- same CMP109/CMP119/CMP122 trajectory, and identify that trajectory with the
-- fields above.  Finite C,L and small-gamma existence are downstream theorems.
literalRowACauchyCanonicalTrajectoryLevel : ProofLevel
literalRowACauchyCanonicalTrajectoryLevel = conditional
