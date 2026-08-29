{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanYM4RowACauchySourceToCanonicalGateExact where

------------------------------------------------------------------------
-- ROW A: MIXED-CAUCHY LOCAL CONSTANTS + HISTORY RESPONSE -> CANONICAL GATE
--
-- Current master already proves, from one normalized interaction package,
--
--   |beta_int| <= C g
--
-- and from its mixed coupling derivative package,
--
--   |d_g beta_int| <= L_local.
--
-- The full history-dependent beta law may still have an additional generated
-- history response.  We therefore keep a separate nonnegative
-- `historyDerivativeConstant` and define
--
--   L_total = L_local + L_history.
--
-- This avoids falsely identifying the local mixed-Cauchy derivative with the
-- derivative of the full CMP109/CMP122 generated trajectory.  Once the literal
-- history-response estimate is supplied, Round95's canonical small-coupling
-- theorem chooses
--
--   gamma* = b / (2 (C + L_total + 1))
--
-- and pays both the positivity and shooting gates automatically.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
import Data.Nat.Base as ℕ
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; -_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4PositiveDenominatorQuotientEndpointsExact as Quot
import DASHI.Physics.YangMills.BalabanYM4InteractionLogHessianCauchyGateExact as H
import DASHI.Physics.YangMills.BalabanYM4InteractionMixedCouplingDerivativeGateExact as Mixed
import DASHI.Physics.YangMills.BalabanYM4RowACanonicalSmallCouplingChoiceExact as Choice
import DASHI.Physics.YangMills.BalabanYM4RowACombinedGateCompositionExact as Combined

------------------------------------------------------------------------
-- Source constants.
------------------------------------------------------------------------

record RowACauchySourceConstants : Set where
  field
    gaussianFloor : ℚ
    gaussianFloorPositive : 0ℚ < gaussianFloor
    mixedInteraction : Mixed.MixedInteractionCauchyData

    -- Only the genuinely propagated/history part remains external to the local
    -- mixed-Cauchy package.  It is a source-derived finite constant, not an
    -- artificial exponential-forgetting law for the marginal coupling.
    historyDerivativeConstant : ℚ
    historyDerivativeConstantNonnegative : 0ℚ ≤ historyDerivativeConstant

open RowACauchySourceConstants public

interactionData : RowACauchySourceConstants → H.InteractionCauchyData
interactionData source = Mixed.base (mixedInteraction source)

sourceInteractionConstant : RowACauchySourceConstants → ℚ
sourceInteractionConstant source = H.interactionConstant (interactionData source)

sourceLocalDerivativeConstant : RowACauchySourceConstants → ℚ
sourceLocalDerivativeConstant source =
  Mixed.interactionDerivativeConstant (mixedInteraction source)

sourceDerivativeConstant : RowACauchySourceConstants → ℚ
sourceDerivativeConstant source =
  sourceLocalDerivativeConstant source + historyDerivativeConstant source

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

sourceLocalDerivativeConstantNonnegative :
  (source : RowACauchySourceConstants) →
  0ℚ ≤ sourceLocalDerivativeConstant source
sourceLocalDerivativeConstantNonnegative source =
  let
    mixed = mixedInteraction source
    base = Mixed.base mixed
    denominator = (H.zLower base * H.zLower base) * H.zLower base
    denominatorPositive = Mixed.zLowerCubedPositive mixed
    reciprocalNN = ℚP.<⇒≤
      (Quot.positiveReciprocalPositive denominator denominatorPositive)
  in
  H.mulNN (Mixed.betaDerivativeNumeratorConstantNN mixed) reciprocalNN

sourceDerivativeConstantNonnegative :
  (source : RowACauchySourceConstants) →
  0ℚ ≤ sourceDerivativeConstant source
sourceDerivativeConstantNonnegative source =
  ℚP.+-mono-≤
    (sourceLocalDerivativeConstantNonnegative source)
    (historyDerivativeConstantNonnegative source)

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
-- Literal trajectory carrier.  C,L_total,gamma are no longer free fields.
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

    interactionLower : ∀ j →
      - (sourceInteractionConstant source * coupling j)
      ≤ betaInteraction j

    inverseSquareRelation : ∀ j →
      inverseSquare j * (coupling j * coupling j) ≡ 1ℚ

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

rowACauchyLocalConstantsToCanonicalGammaLevel : ProofLevel
rowACauchyLocalConstantsToCanonicalGammaLevel = machineChecked

rowACauchyCanonicalGateCompositionLevel : ProofLevel
rowACauchyCanonicalGateCompositionLevel = machineChecked

-- Remaining physical seam is source-native: instantiate the literal mixed
-- interaction Cauchy package and positive Gaussian floor, derive the propagated
-- history response constant on the SAME generated trajectory, and identify the
-- trajectory with the fields above.  Local C and L_local plus small-gamma
-- existence are downstream theorems.
literalRowACauchyCanonicalTrajectoryLevel : ProofLevel
literalRowACauchyCanonicalTrajectoryLevel = conditional
