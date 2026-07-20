module DASHI.Physics.Closure.TriadicAnalyticCertificates where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env

------------------------------------------------------------------------
-- Uniform convergence with the intended geometric-tail shape.

record UniformGeometricTailCertificate
  (M : Env.DepthKernelModel)
  (E : Env.ContinuousDepthEnvelope M) : Set₁ where
  field
    geometricTailBound : Nat → Env.Scalar M

    geometricFormula :
      (n : Nat) → Set

    truncationErrorControlled :
      (d : Env.Stream) →
      (n : Nat) →
      Set

    uniformInStream : Set
    boundTendsToZero : Set

    agreesWithEnvelopeConvergence :
      (d : Env.Stream) →
      Env.Converges M
        (λ n → Env.finiteEvaluation M n d)
        (Env.embed E d)

open UniformGeometricTailCertificate public

------------------------------------------------------------------------
-- Quantitative first-difference bounds and topological embedding.

record QuantitativeEmbeddingCertificate
  (M : Env.DepthKernelModel)
  (E : Env.ContinuousDepthEnvelope M) : Set₁ where
  field
    lowerConstant : Env.Scalar M
    upperConstant : Env.Scalar M

    firstDifferenceTwoSidedBound :
      (n : Nat) →
      (x y : Env.Stream) →
      Env.FirstDifferenceAt n x y →
      Set

    lambdaBelowThirdUsed : Set

    compactStreamDomain : Set
    hausdorffScalarCodomain : Set
    homeomorphismOntoImage : Set
    imageCantorLike : Set

    noRealSmoothManifoldPromotion : Set

open QuantitativeEmbeddingCertificate public

------------------------------------------------------------------------
-- Weighted infinite-axis summability.

record WeightedAxisSummabilityCertificate
  (M : Env.DepthKernelModel)
  (E : Env.ContinuousDepthEnvelope M) : Set₁ where
  field
    Axis : Set
    axisWeight : Axis → Env.Scalar M
    signal : Axis → Env.Stream

    coordinateValue : Axis → Env.Scalar M
    coordinateMatchesEnvelope :
      (ω : Axis) →
      Set

    finiteWeightMassOrSignalDominatingBound : Set
    finiteSupportEnergy : Nat → Env.Scalar M
    finiteSupportEnergyCorrect : (n : Nat) → Set

    energyCauchy : Set
    weightedL2LimitExists : Set

open WeightedAxisSummabilityCertificate public

------------------------------------------------------------------------
-- Native non-Archimedean analytic-manifold lane.

record PAdicAnalyticManifoldCertificate : Set₁ where
  field
    BaseField : Set
    Carrier : Set
    Chart : Set

    chartDimension : Nat
    carrierIsZ3OrCompactOpenDomain : Set
    chartMapsIntoBaseField : Set
    analyticTransitionMaps : Set

    distinctFromRealSmoothStructure : Set
    compatibleWithFiniteQuotientTower : Set

open PAdicAnalyticManifoldCertificate public

------------------------------------------------------------------------
-- Claim boundary.

analyticCertificateStatement : String
analyticCertificateStatement =
  "Convergence, injectivity/topology, weighted-axis summability, and p-adic analytic smoothness are four separate certificates tied to the same digit filtration."

analyticCertificateBoundary : String
analyticCertificateBoundary =
  "The Euclidean Cantor embedding is not a real smoothification of Z_3. Uniform finite-tail bounds, first-difference inequalities, compact-to-Hausdorff embedding, weighted-l2 convergence, and p-adic analytic charts must each be discharged by their own instance."
