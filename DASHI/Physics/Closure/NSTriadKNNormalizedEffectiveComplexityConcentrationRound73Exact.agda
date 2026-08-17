module DASHI.Physics.Closure.NSTriadKNNormalizedEffectiveComplexityConcentrationRound73Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Classical finite Cauchy--Schwarz inequality; DOI not applicable.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Historical conference article; no DOI assigned.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- ROUND73 / NORMALIZED EFFECTIVE COMPLEXITY
--
-- Round72 replaced raw atom cardinality by a same-object factorization
--
--      a_tau = x_tau y_tau,
--      Q = sum x_tau^2,
--      W = sum y_tau^2,
--
-- and proved
--
--      (sum a_tau)^2 <= Q W.
--
-- Raw counting corresponds to y_tau=1 and can incur a fatal dyadic loss.
-- The strongest division-free target is instead a PHYSICALLY NORMALIZED
-- factorization with
--
--      W <= 1.
--
-- Then
--
--      (sum a_tau)^2 <= Q W <= Q,
--
-- so normalization removes the effective-cardinality loss completely.  This
-- mirrors the existing B/Gram discipline: normalization must be constructed
-- on the physical row before any special overlap sharpening is accepted.
--
-- The second theorem composes this directly with Round72's non-circular
-- amplification theorem.  If critical excess mu feeds the SAME structured
-- remainder and its physical overlay is normalized, then
--
--      mu^2 <= Q.
--
-- Thus mu^2 itself is a candidate physical charge floor.  No square root,
-- reciprocal complexity, rational division, or ambient Xi bound is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNFactorizedEffectiveComplexityCauchyRound72Exact as Effective
import DASHI.Physics.Closure.NSTriadKNStructuredTriadicFactorizationOverlayRound72Exact as Overlay
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact as Structured
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationForcesRemainderRound69Exact as Amplification
import DASHI.Physics.Closure.NSTriadKNCriticalRatioNormalizationRound63Exact as C1
import DASHI.Physics.Closure.NSTriadKNCriticalRemainderTriadicCauchyRound71Exact as R71
import DASHI.Physics.Closure.NSTriadKNCriticalAmplificationFactorizedConcentrationRound72Exact as Factorized

record NormalizedEffectiveComplexity
    {atoms : List Structured.LocalizedPDEAtom}
    (overlay : Overlay.TriadicFactorizationOverlay atoms) : Set where
  field
    complexityBelowOne : Overlay.overlayEffectiveComplexity overlay ≤ 1ℚ

open NormalizedEffectiveComplexity public

normalizedOverlayProductBelowCharge :
  ∀ {atoms}
    {overlay : Overlay.TriadicFactorizationOverlay atoms} →
  NormalizedEffectiveComplexity overlay →
  Overlay.overlayCharge overlay * Overlay.overlayEffectiveComplexity overlay
    ≤ Overlay.overlayCharge overlay
normalizedOverlayProductBelowCharge {overlay = overlay} normalized =
  let
    chargeNN : 0ℚ ≤ Overlay.overlayCharge overlay
    chargeNN =
      Effective.concentrationChargeNonnegative (Overlay.overlayFactors overlay)

    complexityNN : 0ℚ ≤ Overlay.overlayEffectiveComplexity overlay
    complexityNN =
      Effective.effectiveComplexityNonnegative (Overlay.overlayFactors overlay)

    productBelowOne :
      Overlay.overlayCharge overlay * Overlay.overlayEffectiveComplexity overlay
      ≤ Overlay.overlayCharge overlay * 1ℚ
    productBelowOne =
      L2.nonnegativeProductMonotone
        chargeNN complexityNN chargeNN ℚP.0≤1
        ℚP.≤-refl (complexityBelowOne normalized)
  in
  subst
    (λ upper →
      Overlay.overlayCharge overlay * Overlay.overlayEffectiveComplexity overlay
      ≤ upper)
    (ℚP.*-identityʳ (Overlay.overlayCharge overlay))
    productBelowOne

normalizedOverlayCauchyRemovesEffectiveComplexity :
  ∀ {atoms}
    (overlay : Overlay.TriadicFactorizationOverlay atoms) →
  NormalizedEffectiveComplexity overlay →
  L2.square (R71.triadicSignedSum atoms)
    ≤ Overlay.overlayCharge overlay
normalizedOverlayCauchyRemovesEffectiveComplexity overlay normalized =
  ℚP.≤-trans
    (Overlay.overlayCauchy overlay)
    (normalizedOverlayProductBelowCharge normalized)

criticalAmplificationForcesNormalizedCharge :
  ∀ {balances block}
    {positiveBlock : C1.PositiveCriticalBlockScale balances block}
    (step : Amplification.CriticalRatioStepDecomposition positiveBlock)
    (n : Nat) (mu : ℚ)
    (atoms : List Structured.LocalizedPDEAtom)
    (overlay : Overlay.TriadicFactorizationOverlay atoms) →
  NormalizedEffectiveComplexity overlay →
  0ℚ ≤ mu →
  Amplification.inherited step n + mu
    ≤ C1.normalizedCriticalRatio positiveBlock (suc n) →
  Amplification.remainder step n ≡ R71.triadicSignedSum atoms →
  L2.square mu ≤ Overlay.overlayCharge overlay
criticalAmplificationForcesNormalizedCharge
    step n mu atoms overlay normalized muNN excess remainderExact =
  ℚP.≤-trans
    (Factorized.criticalAmplificationForcesFactorizedConcentration
      step n mu atoms overlay muNN excess remainderExact)
    (normalizedOverlayProductBelowCharge normalized)

round73NormalizedEffectiveComplexityRemovesCardinalityLoss : Bool
round73NormalizedEffectiveComplexityRemovesCardinalityLoss = true

round73CriticalAmplificationGivesSquareChargeFloorWhenNormalized : Bool
round73CriticalAmplificationGivesSquareChargeFloorWhenNormalized = true

round73PhysicalNormalizedTriadicOverlayConstructed : Bool
round73PhysicalNormalizedTriadicOverlayConstructed = false

round73NormalizedEffectiveComplexityRemovesCardinalityLossIsTrue :
  round73NormalizedEffectiveComplexityRemovesCardinalityLoss ≡ true
round73NormalizedEffectiveComplexityRemovesCardinalityLossIsTrue = refl

round73PhysicalNormalizedTriadicOverlayConstructedIsFalse :
  round73PhysicalNormalizedTriadicOverlayConstructed ≡ false
round73PhysicalNormalizedTriadicOverlayConstructedIsFalse = refl
