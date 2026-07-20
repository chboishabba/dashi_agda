module DASHI.Physics.Closure.TriadicVerifiedLimitAssembly where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env
import DASHI.Foundations.TriadicFiniteQuotient as Q
import DASHI.Algebra.TriadicFiniteIrrep as Irrep
import DASHI.Physics.Closure.TriadicSectorQSeries as QS
import DASHI.Physics.Closure.TriadicModularAutomorphicGate as Modular
import DASHI.Geometry.TriadicEllipticModuliGate as Elliptic

------------------------------------------------------------------------
-- Optional gated lanes.

data Optional (A : Set) : Set where
  absent : Optional A
  present : A → Optional A

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
      SectorAtDepth (Agda.Builtin.Nat.suc n)

    Observable : Set
    sectorObservable :
      (n : Nat) →
      SectorAtDepth n →
      Observable

    stabilizesFrom : Nat
    stabilizationLaw : (n : Nat) → Set

open ModeStabilizationCertificate public

------------------------------------------------------------------------
-- Finite-support energies plus a separate limit theorem.

record WeightedEnergyLimitCertificate : Set₁ where
  field
    Energy : Set
    finiteEnergy : Nat → Energy
    Distance : Energy → Energy → Set

    cauchyLaw : (requestedDepth : Nat) → Set
    dominatingBound : Set
    limitExists : Set

open WeightedEnergyLimitCertificate public

------------------------------------------------------------------------
-- Native p-adic analytic lane remains separate from the Euclidean envelope.

record PAdicAnalyticLane : Set₁ where
  field
    BaseField : Set
    ChartDomain : Set
    chartDimension : Nat
    locallyModelledOnBaseField : Set
    analyticTransitionMaps : Set
    chartDomainRepresentsZ3 : Set

open PAdicAnalyticLane public

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

    finiteCharacterTransform :
      (n : Nat) →
      Irrep.FiniteCharacterTransform n

    modeStabilization : ModeStabilizationCertificate
    weightedEnergyLimit : WeightedEnergyLimitCertificate

    qSeriesCarrier : QS.QSeriesCarrier
    sectorTraceTower : QS.SectorTraceTower qSeriesCarrier

    modularTransformation :
      Optional
        (Modular.ModularTransformationGate
          qSeriesCarrier
          sectorTraceTower)

    ellipticCoefficientRing : Elliptic.EllipticCoefficientRing
    ellipticOrigin :
      Optional
        (Elliptic.EllipticOriginGate ellipticCoefficientRing)

    pAdicAnalyticLane : PAdicAnalyticLane

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
  "The solution is an inverse-system assembly: exact residues and compatible kernels at every depth, exact finite character transforms, trace q-series, proof-carrying tails, mode stabilization, and weighted-energy limits. Modular and elliptic lanes remain optional gated refinements."

verifiedLimitBoundary : String
verifiedLimitBoundary =
  "Finite verification does not imply an infinite theorem without the supplied tail, stabilization, Cauchy, or domination certificates. A real smooth structure on native Z_3 is neither required nor promoted."
