module DASHI.Physics.Closure.BalancedTernaryVerifiedAssembly where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Env
import DASHI.Physics.Closure.BalancedTernaryAnalyticCrossPollination as Cross

------------------------------------------------------------------------
-- Verified-assembly strategy.
--
-- The analytic programme need not wait for one monolithic construction of
-- real analysis, p-adic analysis, weighted Hilbert spaces, and statistical
-- MDL consistency.  Instead, finite exact objects and certified enclosures
-- can be assembled behind explicit interfaces.  The assembly theorem says
-- only that all named receipts are present; it does not strengthen any one
-- receipt into a global analytic theorem.

------------------------------------------------------------------------
-- Finite exact reconstruction lane

record FiniteExactCodec : Set₁ where
  field
    Source : Set
    Code : Set
    compress : Source → Code
    reconstruct : Code → Source
    reconstructCompress : (x : Source) → reconstruct (compress x) ≡ x

open FiniteExactCodec public

------------------------------------------------------------------------
-- Certified interval/enclosure lane

record CertifiedEnclosure : Set₁ where
  field
    Value : Set
    Interval : Set
    enclose : Value → Interval
    Contains : Interval → Value → Set
    enclosureCorrect : (x : Value) → Contains (enclose x) x

open CertifiedEnclosure public

record CertifiedFiniteSum
  (C : CertifiedEnclosure) : Set₁ where
  field
    Term : Set
    evaluateTerm : Term → Value C
    aggregate : Nat → (Nat → Term) → Interval C
    aggregateContainsFiniteSum : Set

open CertifiedFiniteSum public

------------------------------------------------------------------------
-- Truncation plus tail certificate.
--
-- This is the main bypass around an unavailable infinite-sum implementation:
-- compute an exact finite approximant and attach a proof-carrying tail bound.

record TruncationTailCertificate
  (M : Env.DepthKernelModel) : Set₁ where
  field
    stream : Env.Stream
    depth : Nat
    approximant : Env.Scalar M
    approximantMatchesFiniteEvaluation :
      approximant ≡ Env.finiteEvaluation M depth stream
    tailBound : Env.Scalar M
    tailBoundValid : Set

open TruncationTailCertificate public

------------------------------------------------------------------------
-- Finite first-difference metric certificate.
--
-- This discharges practical topology queries at a chosen depth without first
-- requiring a completed global metric-space library.

record FiniteCylinderMetricCertificate
  (M : Env.DepthKernelModel) : Set₁ where
  field
    left right : Env.Stream
    inspectedDepth : Nat
    prefixDecision : Bool
    metricEnclosure : Set
    decisionSound : Set

open FiniteCylinderMetricCertificate public

------------------------------------------------------------------------
-- Finite-axis energy assembly.
--
-- A finite support witness gives an executable energy object.  Infinite-axis
-- summability remains a limit theorem relating a chain of these finite objects.

record FiniteAxisEnergy
  (M : Env.DepthKernelModel)
  (E : Env.ContinuousDepthEnvelope M) : Set₁ where
  field
    Axis : Set
    activeCount : Nat
    activeAxis : Nat → Axis
    signal : Axis → Env.Stream
    finiteEnergy : Env.Scalar M
    finiteEnergyCorrect : Set

open FiniteAxisEnergy public

record SummabilityFromFiniteAssemblies
  (M : Env.DepthKernelModel)
  (E : Env.ContinuousDepthEnvelope M) : Set₁ where
  field
    stage : Nat → FiniteAxisEnergy M E
    cauchyOrDominated : Set
    limitExists : Set

open SummabilityFromFiniteAssemblies public

------------------------------------------------------------------------
-- Finite MDL search lane.
--
-- For a bounded search depth, existence of a selected model is computational
-- rather than asymptotic.  Statistical consistency is deliberately separate.

record FiniteMDLSearch
  (M : Env.DepthPriorMDLModel) : Set₁ where
  field
    maximumDepth : Nat
    selectedDepth : Nat
    selectedWithinBound : Set
    selectedBeatsEveryBoundedCandidate : Set

open FiniteMDLSearch public

------------------------------------------------------------------------
-- Assembly bundle

record BalancedTernaryVerifiedAssembly : Set₁ where
  field
    kernelModel : Env.DepthKernelModel
    continuousEnvelope : Env.ContinuousDepthEnvelope kernelModel

    convergenceCertificate :
      Cross.ConvergenceCertificate kernelModel

    topologyCertificate :
      Cross.TopologicalEmbeddingCertificate
        kernelModel
        continuousEnvelope

    finiteReconstruction : FiniteExactCodec
    certifiedEnclosure : CertifiedEnclosure

    finiteMetricReceipt :
      FiniteCylinderMetricCertificate kernelModel

    finiteEnergyReceipt :
      FiniteAxisEnergy kernelModel continuousEnvelope

    mdlModel : Env.DepthPriorMDLModel
    finiteMDLReceipt : FiniteMDLSearch mdlModel

    pAdicAnalyticLaneKeptSeparate : Bool
    realSmoothificationNotRequired : Bool
    asymptoticMDLConsistencyNotInferred : Bool

open BalancedTernaryVerifiedAssembly public

------------------------------------------------------------------------
-- Explicit status and interpretation

verifiedAssemblyStrategy : String
verifiedAssemblyStrategy =
  "Bypass monolithic analytic blockage by assembling exact finite reconstruction, certified truncation tails, finite-depth topology receipts, finite-support energy receipts, and bounded MDL search. Promote an infinite or asymptotic theorem only when its separate limit certificate is supplied."

smoothnessBypass : String
smoothnessBypass =
  "No real smooth structure on Z_3 is needed for computation: use p-adic analytic charts natively, Euclidean Cantor embeddings externally, and proof-carrying finite approximants at their interface."

finiteDoesNotImplyInfinite : String
finiteDoesNotImplyInfinite =
  "An arbitrary number of verified finite cases does not prove convergence, global topology equivalence, infinite-axis summability, or statistical MDL consistency; each requires its own uniform or limiting argument."

canonicalStatus : Cross.AnalyticStatus
canonicalStatus = Cross.currentAnalyticStatus

realSmoothificationStillFalse :
  Cross.AnalyticStatus.realSmoothZ3Supported canonicalStatus ≡ false
realSmoothificationStillFalse = refl

pAdicAnalyticLaneStillPlausible :
  Cross.AnalyticStatus.pAdicAnalyticZ3Plausible canonicalStatus ≡ true
pAdicAnalyticLaneStillPlausible = refl
