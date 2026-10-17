module DASHI.Cognition.Teleodynamics.LilaE8AttentionBiasExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- LILA-E8 ROOT-CONDITIONED ATTENTION BIAS
--
-- Inspected implementation shape:
--   score = baseline + beta * <q8,r_h> * <k8,r_h>.
-- The extra term is a rank-one bilinear perturbation along a supplied root
-- direction.  Setting beta=0 reduces exactly to the baseline score; that
-- ablation leaves any separate E8 quantizer untouched.
------------------------------------------------------------------------

record RankOneAttentionBias : Set where
  constructor rankOneAttentionBias
  field
    sourceLabel : String
    baselineScore : String
    queryProjection : String
    keyProjection : String
    rootDirection : String
    scaleLabel : String
    biasTermLabel : String
    biasedScore : String
    zeroScale : Bool
    zeroScaleIdentity : zeroScale ≡ true → biasedScore ≡ baselineScore

open RankOneAttentionBias public

zeroScaleReducesToBaseline :
  (b : RankOneAttentionBias) →
  zeroScale b ≡ true →
  biasedScore b ≡ baselineScore b
zeroScaleReducesToBaseline b = zeroScaleIdentity b

record E8AttentionBoundary : Set where
  constructor e8AttentionBoundary
  field
    e8RootDirectionsUsed : Bool
    e8EquivarianceEstablished : Bool
    weylInvarianceEstablished : Bool
    representationIntertwinerEstablished : Bool
    zeroScaleDisablesQuantizer : Bool

open E8AttentionBoundary public

canonicalE8AttentionBoundary : E8AttentionBoundary
canonicalE8AttentionBoundary =
  e8AttentionBoundary true false false false false

demoZeroScaleBias : RankOneAttentionBias
demoZeroScaleBias =
  rankOneAttentionBias
    "visible sovereign-lila-e8 engineering implementation"
    "baseline"
    "<q_8,r_h>"
    "<k_8,r_h>"
    "r_h"
    "0"
    "0"
    "baseline"
    true
    (λ _ → refl)

demoNonzeroScaleBias : RankOneAttentionBias
demoNonzeroScaleBias =
  rankOneAttentionBias
    "visible sovereign-lila-e8 engineering implementation"
    "baseline"
    "<q_8,r_h>"
    "<k_8,r_h>"
    "r_h"
    "beta_h"
    "beta_h <q_8,r_h><k_8,r_h>"
    "baseline + beta_h <q_8,r_h><k_8,r_h>"
    false
    (λ ())
