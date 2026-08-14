module DASHI.Cognition.PNF.DynamicMultimodalTransitionGeometryExact where

------------------------------------------------------------------------
-- DYNAMICAL-GEOMETRIC CROSS-MODAL EQUIVALENCE
--
-- ApproximateMultimodalFutureEquivalenceExact bounds consumer outputs from
-- nearby modality encodings.  Here the latent update process itself is part of
-- the certificate: if every query update is non-expansive, initial cross-modal
-- proximity is preserved for every finite update trace.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.ApproximateMultimodalFutureEquivalenceExact as Approx

record NonExpansiveLatentDynamics (Latent Query : Set) : Set₁ where
  constructor nonExpansiveLatentDynamics
  field
    latentMetric : Approx.NatMetric Latent
    update : Query → Latent → Latent
    updateNonExpansive :
      (query : Query) (left right : Latent) →
      Approx.distance latentMetric (update query left) (update query right)
      ≤ Approx.distance latentMetric left right

open NonExpansiveLatentDynamics public

runUpdates : ∀ {Latent Query} →
  NonExpansiveLatentDynamics Latent Query →
  List Query → Latent → Latent
runUpdates dynamics [] latent = latent
runUpdates dynamics (query ∷ queries) latent =
  runUpdates dynamics queries (update dynamics query latent)

finiteTraceNonExpansive :
  ∀ {Latent Query}
    (dynamics : NonExpansiveLatentDynamics Latent Query)
    (queries : List Query) (left right : Latent) →
  Approx.distance (latentMetric dynamics)
    (runUpdates dynamics queries left)
    (runUpdates dynamics queries right)
  ≤ Approx.distance (latentMetric dynamics) left right
finiteTraceNonExpansive dynamics [] left right = ≤-refl
finiteTraceNonExpansive dynamics (query ∷ queries) left right =
  ≤-trans
    (finiteTraceNonExpansive dynamics queries
      (update dynamics query left)
      (update dynamics query right))
    (updateNonExpansive dynamics query left right)

record DynamicCrossModalEncoding
    (Text Visual Latent Query : Set) : Set₁ where
  constructor dynamicCrossModalEncoding
  field
    dynamics : NonExpansiveLatentDynamics Latent Query
    encodeText : Text → Latent
    encodeVisual : Visual → Latent

open DynamicCrossModalEncoding public

crossModalUpdateGeometryBound :
  ∀ {Text Visual Latent Query}
    (system : DynamicCrossModalEncoding Text Visual Latent Query)
    {text : Text} {visual : Visual} {eta : Nat} →
  Approx.distance (latentMetric (dynamics system))
    (encodeText system text) (encodeVisual system visual)
  ≤ eta →
  (queries : List Query) →
  Approx.distance (latentMetric (dynamics system))
    (runUpdates (dynamics system) queries (encodeText system text))
    (runUpdates (dynamics system) queries (encodeVisual system visual))
  ≤ eta
crossModalUpdateGeometryBound system initialBound queries =
  ≤-trans
    (finiteTraceNonExpansive (dynamics system) queries
      (encodeText system _)
      (encodeVisual system _))
    initialBound

record DynamicGeometricEquivalenceCertificate
    {Text Visual Latent Query : Set}
    (system : DynamicCrossModalEncoding Text Visual Latent Query)
    (text : Text) (visual : Visual) (eta : Nat) : Set₁ where
  constructor dynamicGeometricEquivalenceCertificate
  field
    initialGeometry :
      Approx.distance (latentMetric (dynamics system))
        (encodeText system text) (encodeVisual system visual) ≤ eta
    everyUpdateTrace :
      (queries : List Query) →
      Approx.distance (latentMetric (dynamics system))
        (runUpdates (dynamics system) queries (encodeText system text))
        (runUpdates (dynamics system) queries (encodeVisual system visual))
      ≤ eta

open DynamicGeometricEquivalenceCertificate public

certifyDynamicCrossModalGeometry :
  ∀ {Text Visual Latent Query}
    (system : DynamicCrossModalEncoding Text Visual Latent Query)
    {text : Text} {visual : Visual} {eta : Nat} →
  Approx.distance (latentMetric (dynamics system))
    (encodeText system text) (encodeVisual system visual) ≤ eta →
  DynamicGeometricEquivalenceCertificate system text visual eta
certifyDynamicCrossModalGeometry system initial =
  dynamicGeometricEquivalenceCertificate
    initial
    (crossModalUpdateGeometryBound system initial)

------------------------------------------------------------------------
-- This is deliberately stronger than present-task equivalence and different
-- from output-only future equivalence: it constrains how the latent states move
-- under every finite query/update trace.
------------------------------------------------------------------------
