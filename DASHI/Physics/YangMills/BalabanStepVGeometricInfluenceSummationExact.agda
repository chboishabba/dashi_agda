module DASHI.Physics.YangMills.BalabanStepVGeometricInfluenceSummationExact where

------------------------------------------------------------------------
-- PRIMARY AUTHORITY
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- PURPOSE
--
-- Separate the already-owned finite shell assembly from the one genuinely
-- analytic scalar step.  A geometric summation kernel consumes the strict
-- common ratio and bounds every finite majorant partial sum uniformly.  Order
-- transitivity then gives the corresponding uniform activity/influence bound.
-- No mixing, log-Sobolev or measure-dependent hypothesis is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanClayGate4OscillationAnimalInfluenceExact as Influence
import DASHI.Physics.YangMills.BalabanP06A1A2A3InfluenceExact as A123
open import DASHI.Physics.YangMills.CompactLieProofLevel

record GeometricInfluenceSummationKernel
    {Scale Bound : Set}
    (algebra : Influence.InfluenceAlgebra Bound)
    (inputs :
      A123.PhysicalA1A2A3InfluenceInputs
        {Scale = Scale} {Bound = Bound} algebra) : Set₁ where
  field
    transitive :
      ∀ {left middle right} →
      Influence.InfluenceAlgebra.LessEqual algebra left middle →
      Influence.InfluenceAlgebra.LessEqual algebra middle right →
      Influence.InfluenceAlgebra.LessEqual algebra left right

    uniformBound : Scale → Bound

    majorantPartialSumsUniformlyBounded :
      ∀ (scale : Scale) (cutoff : Nat) →
      Influence.InfluenceAlgebra.LessEqual algebra
        (Influence.partialSum algebra
          (Influence.OscillationAnimalShells.shellMajorant
            (A123.PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale))
          cutoff)
        (uniformBound scale)

open GeometricInfluenceSummationKernel public

record UniformInfluenceBoundCertificate
    {Scale Bound : Set}
    (algebra : Influence.InfluenceAlgebra Bound) : Set₁ where
  field
    uniformInfluence :
      Influence.UniformPolymerInfluence Scale Bound algebra

    bound : Scale → Bound

    activityPartialSumsBounded :
      ∀ (scale : Scale) (cutoff : Nat) →
      Influence.InfluenceAlgebra.LessEqual algebra
        (Influence.partialSum algebra
          (Influence.OscillationAnimalShells.shellActivity
            (Influence.UniformPolymerInfluence.shellsAt
              uniformInfluence scale))
          cutoff)
        (bound scale)

open UniformInfluenceBoundCertificate public

uniformInfluenceBoundFromGeometricSummation :
  ∀ {Scale Bound : Set}
    {algebra : Influence.InfluenceAlgebra Bound}
    {inputs :
      A123.PhysicalA1A2A3InfluenceInputs
        {Scale = Scale} {Bound = Bound} algebra} →
  GeometricInfluenceSummationKernel
    {Scale = Scale} {Bound = Bound} algebra inputs →
  UniformInfluenceBoundCertificate
    {Scale = Scale} {Bound = Bound} algebra
uniformInfluenceBoundFromGeometricSummation
  {inputs = inputs} summation =
  let uniform = A123.canonicalUniformPolymerInfluence inputs
  in record
       { uniformInfluence = uniform
       ; bound =
           GeometricInfluenceSummationKernel.uniformBound summation
       ; activityPartialSumsBounded = λ scale cutoff →
           GeometricInfluenceSummationKernel.transitive summation
             (A123.finiteRootedInfluenceAssembly inputs scale cutoff)
             (GeometricInfluenceSummationKernel.majorantPartialSumsUniformlyBounded
               summation scale cutoff)
       }

stepVGeometricInfluenceCompositionLevel : ProofLevel
stepVGeometricInfluenceCompositionLevel = machineChecked

stepVScalarGeometricSummationKernelLevel : ProofLevel
stepVScalarGeometricSummationKernelLevel = conditional
