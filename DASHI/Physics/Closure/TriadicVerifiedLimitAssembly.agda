module DASHI.Physics.Closure.TriadicVerifiedLimitAssembly where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Physics.Closure.TriadicSectorQSeries as QS
import DASHI.Physics.Closure.TriadicIrrepTraceBridge as Trace
import DASHI.Physics.Closure.TriadicModularAutomorphicGate as Modular
import DASHI.Geometry.TriadicEllipticModuliGate as Elliptic
import DASHI.Physics.Closure.TriadicAnalyticCertificates as Analytic

------------------------------------------------------------------------
-- Optional gated lanes at Set₁.

data Optional₁ (A : Set₁) : Set₁ where
  absent₁ : Optional₁ A
  present₁ : A → Optional₁ A

------------------------------------------------------------------------
-- Exact finite approximant plus certified tail.

record CertifiedDepthTail
  (M : Env.DepthKernelModel) : Set₁ where
  field
    stream : Env.Stream
    depth : Nat
    approximant : Env.Scalar M

    approximantIsFiniteEvaluation :
      approximant ≡ Env.finiteEvaluation M depth stream

    tailBound : Env.Scalar M
    tailBoundValid : Set

open CertifiedDepthTail public

------------------------------------------------------------------------
-- Stabilization of finite representation sectors.

record ModeStabilizationCertificate : Set₁ where
  field
    SectorAtDepth : Nat → Set
    liftSector :
      (n : Nat) →
      SectorAtDepth n →
      SectorAtDepth (suc n)

    Observable : Set
    sectorObservable :
      (n : Nat) →
      SectorAtDepth n →
      Observable

    stabilizesFrom : Nat
    stabilizationLaw : (n : Nat) → Set

open ModeStabilizationCertificate public

------------------------------------------------------------------------
-- Unified verified assembly.

record TriadicVerifiedLimitAssembly : Set₁ where
  field
    inverseLimitPoint : Q.TriadicInverseLimitPoint
    compatibleKernel : Q.CompatibleKernelFamily

    kernelActsOnInverseLimit : Q.TriadicInverseLimitPoint
    kernelActionMatchesCanonical :
      kernelActsOnInverseLimit
      ≡ Q.applyCompatibleKernel compatibleKernel inverseLimitPoint

    depthKernelModel : Env.DepthKernelModel
    continuousEnvelope : Env.ContinuousDepthEnvelope depthKernelModel

    certifiedTailAtDepth :
      Nat →
      CertifiedDepthTail depthKernelModel

    uniformGeometricTail :
      Analytic.UniformGeometricTailCertificate
        depthKernelModel
        continuousEnvelope

    quantitativeEmbedding :
      Analytic.QuantitativeEmbeddingCertificate
        depthKernelModel
        continuousEnvelope

    weightedAxisSummability :
      Analytic.WeightedAxisSummabilityCertificate
        depthKernelModel
        continuousEnvelope

    qSeriesCarrier : QS.QSeriesCarrier
    irrepTraceBridge : Trace.IrrepTraceBridge qSeriesCarrier

    finiteCharacterTransform :
      (n : Nat) →
      Irrep.FiniteCharacterTransform n

    traceTransformAgreement :
      (n : Nat) →
      finiteCharacterTransform n
      ≡ Trace.transformAtDepth irrepTraceBridge n

    sectorTraceTower : QS.SectorTraceTower qSeriesCarrier
    sectorTraceTowerMatchesBridge :
      sectorTraceTower ≡ Trace.traceTower irrepTraceBridge

    modeStabilization : ModeStabilizationCertificate

    modularTransformation :
      Optional₁
        (Modular.ModularTransformationGate
          qSeriesCarrier
          sectorTraceTower)

    ellipticCoefficientRing : Elliptic.EllipticCoefficientRing
    ellipticOrigin :
      Optional₁
        (Elliptic.EllipticOriginGate ellipticCoefficientRing)

    pAdicAnalyticManifold :
      Analytic.PAdicAnalyticManifoldCertificate

    realSmoothZ3Required : Bool
    realSmoothZ3RequiredIsFalse : realSmoothZ3Required ≡ false

open TriadicVerifiedLimitAssembly public

------------------------------------------------------------------------
-- The assembly does not strengthen absent optional gates.

canonicalRealSmoothRequirementIsFalse :
  (A : TriadicVerifiedLimitAssembly) →
  realSmoothZ3Required A ≡ false
canonicalRealSmoothRequirementIsFalse A =
  realSmoothZ3RequiredIsFalse A

------------------------------------------------------------------------
-- Explicit claim boundary.

verifiedLimitStatement : String
verifiedLimitStatement =
  "The solution is an inverse-system assembly: exact residues and compatible kernels at every depth, finite character transforms linked to block traces, trace q-series, geometric tails, quantitative embedding, weighted-l2 limits, and a native p-adic analytic-manifold certificate. Modular and elliptic lanes remain optional gated refinements."

verifiedLimitBoundary : String
verifiedLimitBoundary =
  "Finite verification does not imply an infinite theorem without the supplied tail, stabilization, Cauchy, domination, or topology certificates. A real smooth structure on native Z_3 is neither required nor promoted."
