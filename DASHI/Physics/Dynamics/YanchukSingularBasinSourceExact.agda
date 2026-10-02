{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.YanchukSingularBasinSourceExact where

open import DASHI.Core.Prelude
import DASHI.Physics.Dynamics.SingularBasinReductionExact as SBR

------------------------------------------------------------------------
-- Source-facing equation owners for:
--
-- S. Yanchuk, S. Wieczorek, H. Jardón-Kojakhmetov, H. Alkhayuon,
-- "Singular Basins in Multiscale Systems: Tunneling between Stable States",
-- Physical Review Letters 137, 147202 (2026),
-- DOI 10.1103/jtkh-9lz5.
--
-- This module records the selected equations and the exact formal obligations
-- needed to promote a concrete analytic/numerical model into the generic basin
-- obstruction layer.  It does NOT manufacture the paper's analytical basin
-- theorem from source metadata.
------------------------------------------------------------------------

record ScalarOps : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    one : Scalar
    _+_ : Scalar → Scalar → Scalar
    _-_ : Scalar → Scalar → Scalar
    _*_ : Scalar → Scalar → Scalar

open ScalarOps public

record PitchforkParameters (O : ScalarOps) : Set where
  open ScalarOps O
  field
    epsilon : Scalar
    a : Scalar
    b : Scalar

open PitchforkParameters public

pitchforkFast :
  (O : ScalarOps) →
  Scalar O →
  Scalar O →
  Scalar O
pitchforkFast O x mu =
  let open ScalarOps O
  in x * (mu - (x * x))

pitchforkSlow :
  (O : ScalarOps) →
  PitchforkParameters O →
  Scalar O →
  Scalar O →
  Scalar O
pitchforkSlow O P x mu =
  let open ScalarOps O
  in epsilon P * (((a P * x) - b P) - mu)

------------------------------------------------------------------------
-- Adaptive active-rotator source surface.
--
-- The paper studies:
--
--   dphi/dt = omega + mu - sin(phi)
--   dmu/dt  = epsilon * (-mu + eta * (1 - sin(phi + alpha)))
--
-- Negation is represented as zero - x so no independent unary operator is
-- required by the carrier.
------------------------------------------------------------------------

record TrigScalarOps : Set₁ where
  field
    scalarOps : ScalarOps
    sin : Scalar scalarOps → Scalar scalarOps

open TrigScalarOps public

record ActiveRotatorParameters (O : TrigScalarOps) : Set where
  open TrigScalarOps O
  open ScalarOps scalarOps
  field
    epsilon : Scalar
    omega : Scalar
    eta : Scalar
    alpha : Scalar

open ActiveRotatorParameters public

activeRotatorFast :
  (O : TrigScalarOps) →
  ActiveRotatorParameters O →
  Scalar (scalarOps O) →
  Scalar (scalarOps O) →
  Scalar (scalarOps O)
activeRotatorFast O P phi mu =
  let open ScalarOps (scalarOps O)
  in (omega P + mu) - sin O phi

activeRotatorSlow :
  (O : TrigScalarOps) →
  ActiveRotatorParameters O →
  Scalar (scalarOps O) →
  Scalar (scalarOps O) →
  Scalar (scalarOps O)
activeRotatorSlow O P phi mu =
  let
    open ScalarOps (scalarOps O)
    oneMinusSin = one - sin O (phi + alpha P)
  in epsilon P * ((zero - mu) + (eta P * oneMinusSin))

------------------------------------------------------------------------
-- Promotion contract.
--
-- A concrete discretisation or exact analytic development can instantiate this
-- only after supplying its own full/reduced basins and a literal mismatch
-- witness.  Once supplied, the generic theorem immediately yields failure of
-- basin preservation.
------------------------------------------------------------------------

record SingularFunnelPromotion
  (Full Reduced : Set) : Set₁ where
  field
    reduction : SBR.BasinReduction Full Reduced
    selectedFunnelFailure :
      SBR.BasinReductionFailure reduction

open SingularFunnelPromotion public

promoted-reduction-not-basin-preserving :
  ∀ {Full Reduced : Set} →
  (P : SingularFunnelPromotion Full Reduced) →
  ¬ SBR.BasinPreserving (reduction P)
promoted-reduction-not-basin-preserving P =
  SBR.failure-refutes-preservation
    (selectedFunnelFailure P)

------------------------------------------------------------------------
-- Source receipt keeps literature claims separate from local theorem status.
------------------------------------------------------------------------

record SingularBasinSourceReceipt : Set where
  constructor singularBasinSourceReceipt
  field
    title : String
    journal : String
    doi : String
    publicationDate : String
    sourceStudiesPitchfork : Bool
    sourceStudiesAdaptiveRotator : Bool
    sourceStudiesAdaptiveRotatorNetwork : Bool
    sourceReportsSingularFunnels : Bool
    sourceReportsReductionFailureRisk : Bool
    localAnalyticPitchforkBasinProofComplete : Bool
    localAdaptiveRotatorBasinProofComplete : Bool

canonicalYanchukReceipt : SingularBasinSourceReceipt
canonicalYanchukReceipt =
  singularBasinSourceReceipt
    "Singular Basins in Multiscale Systems: Tunneling between Stable States"
    "Physical Review Letters 137, 147202"
    "10.1103/jtkh-9lz5"
    "2026-09-28"
    true
    true
    true
    true
    true
    false
    false
