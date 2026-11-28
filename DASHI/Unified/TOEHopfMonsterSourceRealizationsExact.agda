module DASHI.Unified.TOEHopfMonsterSourceRealizationsExact where

-- Native consumers of the ORIGINAL source types, not another realization API.
-- Source-written; kernel acceptance not yet observed.
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.List.Base using (_∷_; [])
open import Data.Product using (_×_; _,_)
open import Agda.Primitive using (lzero)

import DASHI.Unified.TOESectorRealizationExact as R
import DASHI.Core.CoarseFineRelativeFibreExact as CF
import DASHI.Physics.Foundations.Hopf369PhaseRetainingObserverCubeExact as Hopf
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as H
import DASHI.Moonshine.MonsterSpecialGravityKKWeightTwoCrosswalkExact as Gravity
import DASHI.Moonshine.MonsterSpecialGravityKKRefinedCoordinateBidiExact as FLM

open import DASHI.Physics.Foundations.TSFVKKHorizontalReductionNoninjectiveBidiExact public
  using (originalFiveMetricVerticalProbeReadsFibreRadius;
         originalFourMetricCannotUniquelyLiftFibreRadius;
         originalFiveMetricMixedVerticalDifferenceReadsConnection;
         originalFourMetricCannotRecoverUniqueChartConnection)

-- Actual coordinate BIDI, deliberately only shared-carrier grade.
-- Existing inverse theorems are consumed verbatim.
gravityFLMCoordinateRealization :
  R.SectorRealization Gravity.GravityCandidateCoordinate FLM.RefinedFLMWeightTwoCoordinate
gravityFLMCoordinateRealization = record
  { sourceSector = R.generalRelativitySector
  ; targetSector = R.monster3BSector
  ; realize = FLM.gravityToRefinedFLM
  ; relationKind = R.equivalenceIsomorphism
  ; attainedGrade = R.sharedCarrier
  ; unpaidObligations =
      R.representationActionAgreement ∷ R.dynamicsEquivariance ∷
      R.actionHamiltonianAgreement ∷ R.metricVariationCommutes ∷
      R.stressObservableAgreement ∷ R.scaleCalibrationAgreement ∷
      R.empiricalSameObjectAttachment ∷ R.heldOutPredictionReceipt ∷
      R.independentReplicationReceipt ∷ []
  ; PreservationWitness =
      ((x : Gravity.GravityCandidateCoordinate) →
        FLM.refinedFLMToGravity (FLM.gravityToRefinedFLM x) ≡ x) ×
      ((y : FLM.RefinedFLMWeightTwoCoordinate) →
        FLM.gravityToRefinedFLM (FLM.refinedFLMToGravity y) ≡ y)
  ; preservationWitness = FLM.gravityToFLMToGravity , FLM.flmToGravityToFLM
  ; externalPromotion = false
  ; externalPromotionIsFalse = refl
  ; reading = "Literal original gravity/FLM coordinate inverse, not physical group or action equivalence."
  }

module Spectral (F : C3.RealField lzero)
  (E : C3.IntegerEmbedding F) (I : C3.ModeInverseSquare F E)
  (S : H.HelicalModeScalars F) where

  module P = Hopf.Spectral F E I S

  -- The ACTUAL cut datum is reopened from its tag and full original datum.
  -- No lossy projection of the phase, helicity, mode, coefficient or zero.
  cutTag : ∀ {n} → P.CutDatum n → Bool
  cutTag (P.retained _) = true
  cutTag (P.omitted _) = false

  joinCut : ∀ {n} → Bool → P.Datum n → P.CutDatum n
  joinCut true a = P.retained a
  joinCut false a = P.omitted a

  joinCutExact : ∀ {n} (a : P.CutDatum n) →
    joinCut (cutTag a) (P.reopen a) ≡ a
  joinCutExact (P.retained a) = refl
  joinCutExact (P.omitted a) = refl

  cutReopening : (n : Nat) → CF.CoarseFineReopening (P.CutDatum n)
  cutReopening n =
    CF.coarseFineReopening Bool (P.Datum n) cutTag P.reopen joinCut joinCutExact

  -- Actual one-step and two-step commutation for the source's indexed
  -- spectral operation. These are not Einstein time evolution.
  module At (select : Z3.FourierMode → Bool) where
    module A = P.At select

    splitRealization : (n : Nat) → R.SectorRealization (P.Datum n) (P.CutDatum n)
    splitRealization n = record
      { sourceSector = R.electromagnetismSector
      ; targetSector = R.hyperfabric369Sector
      ; realize = A.split
      ; relationKind = R.restrictionInclusion
      ; attainedGrade = R.sharedCarrier
      ; unpaidObligations =
          R.representationActionAgreement ∷ R.dynamicsEquivariance ∷
          R.actionHamiltonianAgreement ∷ R.metricVariationCommutes ∷
          R.stressObservableAgreement ∷ R.scaleCalibrationAgreement ∷
          R.empiricalSameObjectAttachment ∷ R.heldOutPredictionReceipt ∷
          R.independentReplicationReceipt ∷ []
      ; PreservationWitness =
          ((a : P.Datum n) → P.reopen (A.split a) ≡ a) ×
          ((a : P.Datum n) → A.split (P.advance a) ≡ P.advanceCut (A.split a))
      ; preservationWitness = A.reopenSplit , A.splitAdvance
      ; externalPromotion = false
      ; externalPromotionIsFalse = refl
      ; reading = "Original indexed helical coefficient split and exact reopening; advance is spectral order, not physical time."
      }

    originalCutAdvanceCommutes :
      ∀ {n} (a : P.Datum n) →
      R.realize (splitRealization (suc n)) (P.advance a) ≡
      P.advanceCut (R.realize (splitRealization n) a)
    originalCutAdvanceCommutes = A.splitAdvance


------------------------------------------------------------------------
-- AP: literal KK graph metric, not a new metric or stress interface.
-- The polynomial path keeps the connection AND graph-coordinate tangent.
-- This is a finite rational bilinear statement, not the determinant,
-- Lorentzian integral or common QFT action variation theorem.
------------------------------------------------------------------------
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Physics.Foundations.TSFVKKSelectedHorizontalMetricSchurExact as KK

kkGraphMetricPathExact :
  ∀ {V : Set}
    (g dg : V → V → ℚ)
    (A dA df ddf : V → ℚ)
    (r dr t : ℚ) (v w : V) →
  KK.KK5Bilinear
    (λ x y → g x y + t * dg x y)
    (λ x → A x + t * dA x) (r + t * dr)
    v (df v + t * ddf v) w (df w + t * ddf w)
  ≡
  g v w + t * dg v w +
    (r + t * dr) *
      (((A v + df v) + t * (dA v + ddf v)) *
       ((A w + df w) + t * (dA w + ddf w)))
kkGraphMetricPathExact g dg A dA df ddf r dr t v w =
  Ring.solve-∀
    (g v w) (dg v w) (A v) (df v) (dA v) (ddf v)
    (A w) (df w) (dA w) (ddf w) r dr t

-- Consume the actual gauge transport at every graph tangent.
-- The original owner uses A -> A+dLambda, df -> df-dLambda.
kkGraphMetricGaugeExact :
  ∀ {V : Set} (g : V → V → ℚ)
    (A df dLambda : V → ℚ) (r : ℚ) (v w : V) →
  KK.KK5Bilinear g (λ x → A x + dLambda x) r
    v (df v - dLambda v) w (df w - dLambda w)
  ≡ KK.KK5Bilinear g A r v (df v) w (df w)
kkGraphMetricGaugeExact g A df dLambda r v w =
  KK.KK5GaugeShiftPreservesBilinear g A dLambda r v w (df v) (df w)


------------------------------------------------------------------------
-- AQ: same original KK quadratic, signed fibre-null endpoints.
-- Positive-radius/causal and real square-root existence are separate
-- physical hypotheses. The rational algebra is exact for supplied p.
------------------------------------------------------------------------

kkGraphNullPositive :
  ∀ {V : Set} (g : V → V → ℚ) (A : V → ℚ)
    (r p : ℚ) (v : V) →
  KK.KK5Bilinear g A r v (p - A v) v (p - A v)
  ≡ g v v + r * (p * p)
kkGraphNullPositive g A r p v =
  Ring.solve-∀ (g v v) (A v) r p

kkGraphNullNegative :
  ∀ {V : Set} (g : V → V → ℚ) (A : V → ℚ)
    (r p : ℚ) (v : V) →
  KK.KK5Bilinear g A r v ((0ℚ - p) - A v)
    v ((0ℚ - p) - A v)
  ≡ g v v + r * (p * p)
kkGraphNullNegative g A r p v =
  Ring.solve-∀ (g v v) (A v) r p

-- Retain both signed endpoints: their sum and difference recover
-- connection and radius-normalized interval width without dividing.
kkSignedEndpointSum :
  (a p : ℚ) →
  (p - a) + ((0ℚ - p) - a) ≡ (0ℚ - a) + (0ℚ - a)
kkSignedEndpointSum a p = Ring.solve-∀ a p

kkSignedEndpointDifference :
  (a p : ℚ) →
  (p - a) - ((0ℚ - p) - a) ≡ p + p
kkSignedEndpointDifference a p = Ring.solve-∀ a p

open import DASHI.Physics.Foundations.TSFVKKFiveMetricInvertibleShearExact public
  using (kkActualFiveBilinearIsInvertibleShearPullback; kkShearLeftInverse; kkShearRightInverse)

open import DASHI.Physics.Foundations.TSFVKKSameArrowQuadraticMetricWeldExact public
  using (sameMetricKKObservedProbeEqualsTSFV; sameMetricKKDirectionFromTSFV)

open import DASHI.Physics.Foundations.TSFVKKFourMetricVerticalProbeFullReconstructionExact public
  using (originalKKFullFiveMetricRecoveredFromThreeProbeFamilies)


------------------------------------------------------------------------
-- BK: exact finite indicial polynomial, source AK5/BJ/BK.
-- The matching-trace domain and Sturm-Liouville integration by parts
-- are analytic obligations, not inferred from this ring identity.
-- Source-written; no kernel acceptance claimed.
------------------------------------------------------------------------

open import Data.Rational.Base using (1ℚ)

normalFirstIndicialFactorization :
  (p : ℚ) →
  p * (p - (1ℚ + 1ℚ)) - (1ℚ + 1ℚ + 1ℚ)
  ≡ (p + 1ℚ) * (p - (1ℚ + 1ℚ + 1ℚ))
normalFirstIndicialFactorization p = Ring.solve-∀ p


------------------------------------------------------------------------
-- BR145: source-indexed G3 tidal observation.
-- BR144 supplies the actual central Ricci jet at analytic scope.
-- The native witness below pays only the rational sign-fibre descent.
------------------------------------------------------------------------

import DASHI.Core.ConsumerDescentMinimalObserverExact as CD
open import DASHI.Core.Prelude using (⊥)

centralTidalEvenReadout : ℚ → ℚ
centralTidalEvenReadout e = e * e

centralTidalEvenSignCollision :
  (e : ℚ) → centralTidalEvenReadout e ≡ centralTidalEvenReadout (0ℚ - e)
centralTidalEvenSignCollision e = Ring.solve-∀ e

centralTidalSignedAmplitude : ℚ → ℚ
centralTidalSignedAmplitude e = e

-- Distinctness is the nonzero signed-source hypothesis.
-- No absolute sign is claimed without a marked fibre orientation.
centralTidalSignNonDescent :
  (e : ℚ) → (e ≡ 0ℚ - e → ⊥) →
  CD.ConsumerNonDescentWitness centralTidalEvenReadout centralTidalSignedAmplitude
centralTidalSignNonDescent e distinct =
  CD.consumerNonDescentWitness e (0ℚ - e)
    (centralTidalEvenSignCollision e) distinct

centralTidalSignBlocksFactorization :
  (e : ℚ) → (e ≡ 0ℚ - e → ⊥) →
  CD.FactorsThrough centralTidalEvenReadout centralTidalSignedAmplitude → ⊥
centralTidalSignBlocksFactorization e distinct =
  CD.nonDescentWitnessBlocksFactorization (centralTidalSignNonDescent e distinct)

-- If the observed, radius-cleared mixed probe is k*e, the sign
-- reversal is exact. BR144 supplies k=16; calibration and division
-- by the physical radius require the actual source and units.
centralTidalMixedSignTransport :
  (k e : ℚ) → k * (0ℚ - e) ≡ 0ℚ - (k * e)
centralTidalMixedSignTransport k e = Ring.solve-∀ k e


------------------------------------------------------------------------
-- BR149: actual central optical and marked mixed readout, cleared
-- of constants. r is the supplied inverse squared fibre radius.
-- Rational ring identities only; nonzero division, physical source
-- and orientation remain explicit in the analytical owner.
------------------------------------------------------------------------

centralJointOptical : ℚ → ℚ → ℚ
centralJointOptical r e = r * (e * e)

centralJointMixed : ℚ → ℚ → ℚ
centralJointMixed r e = r * e

centralJointAmplitudeCross :
  (r e : ℚ) → centralJointOptical r e ≡ e * centralJointMixed r e
centralJointAmplitudeCross r e = Ring.solve-∀ r e

centralJointRadiusCross :
  (r e : ℚ) →
  centralJointMixed r e * centralJointMixed r e
  ≡ r * centralJointOptical r e
centralJointRadiusCross r e = Ring.solve-∀ r e

centralJointZeroOptical : (r : ℚ) → centralJointOptical r 0ℚ ≡ 0ℚ
centralJointZeroOptical r = Ring.solve-∀ r

centralJointZeroMixed : (r : ℚ) → centralJointMixed r 0ℚ ≡ 0ℚ
centralJointZeroMixed r = Ring.solve-∀ r
