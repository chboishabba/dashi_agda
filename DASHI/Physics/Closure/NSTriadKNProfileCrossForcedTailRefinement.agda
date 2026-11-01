module DASHI.Physics.Closure.NSTriadKNProfileCrossForcedTailRefinement where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; _∸_)

import DASHI.Physics.Closure.NSTriadKNAdversarialColumnClosureDependency as AdversarialColumn
import DASHI.Physics.Closure.NSTriadKNTransitionClosureDependency as TransitionClosure
import DASHI.Physics.Closure.NSTriadKNForcedTailRowUniformBound as FTRow
import DASHI.Physics.Closure.NSTriadKNProfileDepthGeometryBase as DepthBase
import DASHI.Physics.Closure.NSTriadKNProfileClassifierDepthSoundnessSurface
  as ClassifierDepthSurface

-----------------------------------------------------------------------
-- Restricted incidence predicates.
--
-- FTToAdversarialIncidence N i j  holds when entry pair (i,j) carries a
-- forced-tail incidence and column j supports adversarial incidences.
-- FTToTransitionIncidence N i j   holds when (i,j) is a forced-tail
-- incidence and column j supports transition incidences.
--
-- These are the correct domains for the weight-orientation gain.  Without
-- the incidence premise, the inequality (suc N) * w(j) ≤ w(i) would be
-- globally false for any sane weight system.
--
-- IMPORTANT:
-- These are no longer free predicates. Each restricted incidence carries
-- the existing classifier landing together with the source/target profile
-- witnesses needed by Blocker 1.
-----------------------------------------------------------------------

ForcedTailSource : Nat → Nat → Set
ForcedTailSource = DepthBase.ForcedTailSource

AdversarialTarget : Nat → Nat → Set
AdversarialTarget = DepthBase.AdversarialTarget

TransitionTarget : Nat → Nat → Set
TransitionTarget = DepthBase.TransitionTarget

pow2 : Nat → Nat
pow2 zero = suc zero
pow2 (suc n) = suc (suc zero) * pow2 n

weightOf : Nat → Nat
weightOf k =
  pow2 (DepthBase.maxDepth ∸ DepthBase.entryDepth k)

record FTToAdversarialIncidence (N i j : Nat) : Set₁ where
  field
    classifierSurface :
      ClassifierDepthSurface.ExistingProfileClassifierSurface

    classifierLanding :
      ClassifierDepthSurface.ExistingFTToAdversarialIncidence
        classifierSurface N i j

    sourceIsForcedTail :
      ForcedTailSource N i

    targetIsAdversarial :
      AdversarialTarget N j

record FTToTransitionIncidence (N i j : Nat) : Set₁ where
  field
    classifierSurface :
      ClassifierDepthSurface.ExistingProfileClassifierSurface

    classifierLanding :
      ClassifierDepthSurface.ExistingFTToTransitionIncidence
        classifierSurface N i j

    sourceIsForcedTail :
      ForcedTailSource N i

    targetIsTransition :
      TransitionTarget N j

classifierLandingSound :
  (N i j : Nat) →
  (inc : FTToAdversarialIncidence N i j) →
  ClassifierDepthSurface.ExistingFTToAdversarialIncidence
    (FTToAdversarialIncidence.classifierSurface inc) N i j
classifierLandingSound N i j inc =
  FTToAdversarialIncidence.classifierLanding inc

FTToAdversarialIncidenceCarriesClassifier :
  (N i j : Nat) →
  (inc : FTToAdversarialIncidence N i j) →
  ClassifierDepthSurface.ExistingFTToAdversarialIncidence
    (FTToAdversarialIncidence.classifierSurface inc) N i j
FTToAdversarialIncidenceCarriesClassifier =
  classifierLandingSound

transitionClassifierLandingSound :
  (N i j : Nat) →
  (inc : FTToTransitionIncidence N i j) →
  ClassifierDepthSurface.ExistingFTToTransitionIncidence
    (FTToTransitionIncidence.classifierSurface inc) N i j
transitionClassifierLandingSound N i j inc =
  FTToTransitionIncidence.classifierLanding inc

FTToTransitionIncidenceCarriesClassifier :
  (N i j : Nat) →
  (inc : FTToTransitionIncidence N i j) →
  ClassifierDepthSurface.ExistingFTToTransitionIncidence
    (FTToTransitionIncidence.classifierSurface inc) N i j
FTToTransitionIncidenceCarriesClassifier =
  transitionClassifierLandingSound

-----------------------------------------------------------------------
-- Weight function postulate.
--
-- The concrete weight assignment w : Nat → Nat maps each entry index to
-- its Schur-test weight.  The weight orientation gain requires:
--
--   For FT→adv column pairs: (suc N) * w(j) ≤ w(i)
--   For FT→trans column pairs: (suc N) * w(j) ≤ w(i)
--
-- This holds if weights decrease with shell depth (coarse = heavy,
-- fine = light) and the shell separation between FT rows and
-- adv/trans columns is at least one scale.
-----------------------------------------------------------------------

-----------------------------------------------------------------------
-- Forced-tail restricted row refinement.
--
-- For the global Schur matrix, the crude row bound R_N^FT <= A_FT is not enough
-- because the column decay for adversarial/transition columns is only N^-1.
--
-- This file defines the restricted row decay theorems where forced-tail row
-- mass landing in non-forced-tail columns gains an extra N^-1 factor:
--
--   R_N^{FT -> adv} <= A / N
--   R_N^{FT -> trans} <= A / N
--
-- Four gain routes are named. Any one suffices to discharge the restricted row.

-----------------------------------------------------------------------
-- FT → Adversarial: gain routes
-----------------------------------------------------------------------

-- Route 1: count gain — restricted column support.
-- Prove: #I^{FT→adv}_{N,c}(i) ≤ N^{-1} * #I^{FT}_{N,c}(i)
record ForcedTailAdversarialCountGain : Set₁ where
  constructor mkForcedTailAdversarialCountGain
  field
    -- at most 1/N of forced-tail row support lands in adversarial columns
    countGainBound : Set

-- Route 2: magnitude gain — extra N^{-1} decay on cross incidences.
-- Prove: m_N(τ) ≤ N^{-1} * μ_{FT}(N,c) on FT→adv incidences
record ForcedTailAdversarialMagnitudeGain : Set₁ where
  constructor mkForcedTailAdversarialMagnitudeGain
  field
    -- forced-tail kernel entries landing in adversarial columns carry
    -- an extra factor of N^{-1}
    magnitudeGainBound : Set

-- Route 3: weight orientation gain.
-- Prove: w_j / w_i ≤ (N+1)^{-1} for FT→adv incidences.
--
-- In ℕ-scaled arithmetic, the inequality w_j ≤ w_i / (N+1) is encoded as
--
--   (suc N) * w_j ≤ w_i
--
-- This is the priority gain route for Blocker 1 because it is pointwise
-- and does not require a new incidence-count classification.
--
-- CRITICAL: the inequality is conditional on the restricted incidence
-- predicate FTToAdversarialIncidence N i j, NOT over all (i,j).  Without
-- the incidence premise the theorem is globally false for any sane weight
-- system.
record ForcedTailAdversarialWeightOrientationGain : Set₁ where
  constructor mkForcedTailAdversarialWeightOrientationGain
  field
    -- For each shell N, row i, column j that forms an FT→adv incident pair:
    --   (suc N) * w(j) ≤ w(i)
    --
    -- This implies the weight ratio w(j)/w(i) ≤ 1/(N+1) on the restricted
    -- set, giving the required N^{-1} gain.
    weightRatioBound :
      (N i j : Nat) →
      FTToAdversarialIncidence N i j →
      suc N * weightOf j ≤ weightOf i

-- Route 4: profile incompatibility.
-- Prove: FT(τ) ∧ AdvColumn(j) ⇒ extra scale separation / angular loss /
-- projection loss sufficient to produce the N^{-1} factor
record ForcedTailAdversarialProfileIncompatibility : Set₁ where
  constructor mkForcedTailAdversarialProfileIncompatibility
  field
    -- geometric incompatibility estimate
    incompatibilityEstimate : Set

-- Disjunction type: any one gain route suffices
data ForcedTailToAdversarialGainRoute : Set₁ where
  viaCountGain             : ForcedTailAdversarialCountGain → ForcedTailToAdversarialGainRoute
  viaMagnitudeGain         : ForcedTailAdversarialMagnitudeGain → ForcedTailToAdversarialGainRoute
  viaWeightOrientationGain : ForcedTailAdversarialWeightOrientationGain → ForcedTailToAdversarialGainRoute
  viaProfileIncompatibility : ForcedTailAdversarialProfileIncompatibility → ForcedTailToAdversarialGainRoute

-- Restricted row N1: R_N^{FT→adv} ≤ A/N via any gain route
record ForcedTailToAdversarialRestrictedRowN1 : Set₁ where
  constructor mkForcedTailToAdversarialRestrictedRowN1
  field
    gain : ForcedTailToAdversarialGainRoute

-----------------------------------------------------------------------
-- FT → Transition: gain routes
-----------------------------------------------------------------------

-- Route 1: count gain — restricted column support.
record ForcedTailTransitionCountGain : Set₁ where
  constructor mkForcedTailTransitionCountGain
  field
    -- #I^{FT→trans}_{N,c}(i) ≤ N^{-1} * #I^{FT}_{N,c}(i)
    countGainBound : Set

-- Route 2: magnitude gain — extra N^{-1} decay.
record ForcedTailTransitionMagnitudeGain : Set₁ where
  constructor mkForcedTailTransitionMagnitudeGain
  field
    -- m_N(τ) ≤ N^{-1} * μ_{FT}(N,c) on FT→trans incidences
    magnitudeGainBound : Set

-- Route 3: weight orientation gain.
-- (suc N) * w(j) ≤ w(i) conditional on FT→trans incidences.
record ForcedTailTransitionWeightOrientationGain : Set₁ where
  constructor mkForcedTailTransitionWeightOrientationGain
  field
    weightRatioBound :
      (N i j : Nat) →
      FTToTransitionIncidence N i j →
      suc N * weightOf j ≤ weightOf i

-- Route 4: profile incompatibility.
record ForcedTailTransitionProfileIncompatibility : Set₁ where
  constructor mkForcedTailTransitionProfileIncompatibility
  field
    -- FT(τ) ∧ TransColumn(j) ⇒ extra scale separation / angular loss
    incompatibilityEstimate : Set

-- Disjunction type
data ForcedTailToTransitionGainRoute : Set₁ where
  viaCountGain             : ForcedTailTransitionCountGain → ForcedTailToTransitionGainRoute
  viaMagnitudeGain         : ForcedTailTransitionMagnitudeGain → ForcedTailToTransitionGainRoute
  viaWeightOrientationGain : ForcedTailTransitionWeightOrientationGain → ForcedTailToTransitionGainRoute
  viaProfileIncompatibility : ForcedTailTransitionProfileIncompatibility → ForcedTailToTransitionGainRoute

-- Restricted row N1: R_N^{FT→trans} ≤ A/N via any gain route
record ForcedTailToTransitionRestrictedRowN1 : Set₁ where
  constructor mkForcedTailToTransitionRestrictedRowN1
  field
    gain : ForcedTailToTransitionGainRoute

-----------------------------------------------------------------------
-- Cross-product N^{-2} composites
--
-- Restricted row bound + column bound => cross-product N^{-2} bound.
-- These re-export the existing closure-dependency witnesses for the
-- adversarial and transition column sides.
-----------------------------------------------------------------------

record ForcedTailAdversarialCrossProductN2 : Set₁ where
  constructor mkForcedTailAdversarialCrossProductN2
  field
    rowRefinement : ForcedTailToAdversarialRestrictedRowN1
    columnBound   : AdversarialColumn.NSTriadKNAdversarialColumnClosureDependency

record ForcedTailTransitionCrossProductN2 : Set₁ where
  constructor mkForcedTailTransitionCrossProductN2
  field
    rowRefinement : ForcedTailToTransitionRestrictedRowN1
    columnBound   : TransitionClosure.NSTriadKNTransitionColumnClosureDependency

-----------------------------------------------------------------------
-- Composite theorem: weight orientation gain ⇒ restricted row N⁻¹
--
-- If the forced-tail row bound is O(1) and the weight ratio satisfies
-- w_j ≤ w_i / (N+1) on the restricted incidence set, then the restricted
-- row R_N^{FT→adv} ≤ A/(N+1) ≤ A/N follows because each kernel term
-- K_N^FT(i,j) contributes weight ratio w_j/w_i to the row sum, and the
-- weight ratio is ≤ 1/(N+1) on the relevant incidences.
-----------------------------------------------------------------------

forcedTailToAdversarialRestrictedRowN1FromWeight :
  ForcedTailAdversarialWeightOrientationGain →
  ForcedTailToAdversarialRestrictedRowN1
forcedTailToAdversarialRestrictedRowN1FromWeight weightGain =
  mkForcedTailToAdversarialRestrictedRowN1
    (viaWeightOrientationGain weightGain)

forcedTailToTransitionRestrictedRowN1FromWeight :
  ForcedTailTransitionWeightOrientationGain →
  ForcedTailToTransitionRestrictedRowN1
forcedTailToTransitionRestrictedRowN1FromWeight weightGain =
  mkForcedTailToTransitionRestrictedRowN1
    (viaWeightOrientationGain weightGain)

-----------------------------------------------------------------------
-- Current canonical witnesses.
--
-- These are local documentary placeholders only.  The active downstream
-- Blocker 1 route now goes through `NSTriadKNProfileCrossWeightBridge`,
-- which packages the actual depth-bearing weight-orientation terms from
-- `NSTriadKNProfileCrossWeightModel`.
--
-- The postulates below remain here to preserve this theorem surface without
-- introducing an import cycle, but they are no longer the active source of
-- the FT→adv / FT→trans restricted-row or cross-product terms.
-- The gain records inhabit the disjunctions via the WEIGHT ORIENTATION
-- route (Route 3) as the first priority target.  Replace the postulates
-- below with actual proofs once the weight function is constructed.
-----------------------------------------------------------------------

postulate
  canonical_ft_adv_count_gain     : ForcedTailAdversarialCountGain
  canonical_ft_adv_magnitude_gain : ForcedTailAdversarialMagnitudeGain
  canonical_ft_adv_weight_gain    : ForcedTailAdversarialWeightOrientationGain
  canonical_ft_adv_incompat_gain  : ForcedTailAdversarialProfileIncompatibility

  canonical_ft_trans_count_gain     : ForcedTailTransitionCountGain
  canonical_ft_trans_magnitude_gain : ForcedTailTransitionMagnitudeGain
  canonical_ft_trans_weight_gain    : ForcedTailTransitionWeightOrientationGain
  canonical_ft_trans_incompat_gain  : ForcedTailTransitionProfileIncompatibility

-- Canonical choice: inhabit via the WEIGHT ORIENTATION route (Route 3),
-- which is the priority target for Blocker 1.  The weight-orientation
-- path is pointwise and multiplies every existing forced-tail row estimate
-- without needing a new incidence-count classification.
-- Switch to a different route only if weight orientation fails.
canonical_ft_adv_row_n1 : ForcedTailToAdversarialRestrictedRowN1
canonical_ft_adv_row_n1 =
  mkForcedTailToAdversarialRestrictedRowN1
    (viaWeightOrientationGain canonical_ft_adv_weight_gain)

canonical_ft_trans_row_n1 : ForcedTailToTransitionRestrictedRowN1
canonical_ft_trans_row_n1 =
  mkForcedTailToTransitionRestrictedRowN1
    (viaWeightOrientationGain canonical_ft_trans_weight_gain)

canonical_ft_adv_cross : ForcedTailAdversarialCrossProductN2
canonical_ft_adv_cross =
  mkForcedTailAdversarialCrossProductN2
    canonical_ft_adv_row_n1
    AdversarialColumn.canonicalNSTriadKNAdversarialColumnClosureDependency

canonical_ft_trans_cross : ForcedTailTransitionCrossProductN2
canonical_ft_trans_cross =
  mkForcedTailTransitionCrossProductN2
    canonical_ft_trans_row_n1
    TransitionClosure.canonicalNSTriadKNTransitionColumnClosureDependency

-----------------------------------------------------------------------
-- Honest status booleans.
--
-- These track whether each gain route has an analytic inhabitant.
-- They refer only to the placeholder canonicals in this file, not to the
-- bridged downstream route built in `NSTriadKNProfileCrossWeightBridge`.
-----------------------------------------------------------------------

record NSTriadKNProfileCrossForcedTailRefinementStatus : Set where
  constructor mkNSTriadKNProfileCrossForcedTailRefinementStatus
  field
    -- FT→adv routes
    ft-adv-count-gain-proved        : Bool
    ft-adv-magnitude-gain-proved    : Bool
    ft-adv-weight-gain-proved       : Bool
    ft-adv-incompat-gain-proved     : Bool
    ft-adv-row-n1-proved            : Bool
    -- FT→trans routes
    ft-trans-count-gain-proved      : Bool
    ft-trans-magnitude-gain-proved  : Bool
    ft-trans-weight-gain-proved     : Bool
    ft-trans-incompat-gain-proved   : Bool
    ft-trans-row-n1-proved          : Bool
    -- Cross-product composites
    ft-adv-cross-n2-proved          : Bool
    ft-trans-cross-n2-proved        : Bool

open NSTriadKNProfileCrossForcedTailRefinementStatus public

-- ALL FALSE — these placeholder canonicals are intentionally left dormant.
-- The active downstream route is discharged via the separate weight bridge.
currentNSTriadKNProfileCrossForcedTailRefinementStatus :
  NSTriadKNProfileCrossForcedTailRefinementStatus
currentNSTriadKNProfileCrossForcedTailRefinementStatus =
  mkNSTriadKNProfileCrossForcedTailRefinementStatus
    false  -- ft-adv-count-gain-proved
    false  -- ft-adv-magnitude-gain-proved
    false  -- ft-adv-weight-gain-proved
    false  -- ft-adv-incompat-gain-proved
    false  -- ft-adv-row-n1-proved
    false  -- ft-trans-count-gain-proved
    false  -- ft-trans-magnitude-gain-proved
    false  -- ft-trans-weight-gain-proved
    false  -- ft-trans-incompat-gain-proved
    false  -- ft-trans-row-n1-proved
    false  -- ft-adv-cross-n2-proved
    false  -- ft-trans-cross-n2-proved
