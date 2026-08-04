module DASHI.Physics.YangMills.BalabanP06A1A2A3InfluenceExact where

------------------------------------------------------------------------
-- PRIMARY AUTHORITY
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- AUDIT-LEAD BOUNDARY
--
-- User-supplied recent manuscripts identified only as 2602.0070 and
-- 2602.0072 motivate the A1/A2/A3 interface.  Their author/title/DOI metadata
-- has not been authoritatively verified here, so they are not used as theorem
-- inhabitants.  The machine-checked content below is only the finite assembly
-- and canonical-constant wiring already justified by DASHI's owned reducers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy
import DASHI.Physics.YangMills.BalabanP06CanonicalAnimalConstantExact as P06
import DASHI.Physics.YangMills.BalabanClayGate4OscillationAnimalInfluenceExact as Influence
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PhysicalA1A2A3InfluenceInputs
    {Scale Bound : Set}
    (algebra : Influence.InfluenceAlgebra Bound) : Set₁ where
  field
    -- A1 + A3: the physical polymer representation and canonical animal count.
    p06ModelLeaf : Entropy.P06ModelLeafDischargePackage

    -- Embed the owned natural animal constant into the analytic bound carrier.
    embedNat : Nat → Bound
    decayFactor : Bound

    -- A2: each scale supplies the physical per-link oscillation shell bound.
    shellsAt :
      Scale → Influence.OscillationAnimalShells {Scale} algebra

    canonicalWeightedRatio : Bound
    canonicalWeightedRatioMeaning :
      canonicalWeightedRatio
        ≡ Influence.InfluenceAlgebra.multiply algebra
            (embedNat (P06.canonicalAnimalConstant p06ModelLeaf))
            decayFactor

    weightedRatioAtScaleIsCanonical :
      ∀ scale →
      Influence.OscillationAnimalShells.weightedRatio
        (shellsAt scale)
        ≡ canonicalWeightedRatio

    StrictlyLess : Bound → Bound → Set
    one : Bound
    canonicalWeightedRatioBelowOne :
      StrictlyLess canonicalWeightedRatio one

open PhysicalA1A2A3InfluenceInputs public

canonicalP06Certificate :
  ∀ {Scale Bound}
    {algebra : Influence.InfluenceAlgebra Bound} →
  (inputs : PhysicalA1A2A3InfluenceInputs algebra) →
  P06.CanonicalP06AnimalConstantCertificate
    (PhysicalA1A2A3InfluenceInputs.p06ModelLeaf inputs)
canonicalP06Certificate inputs =
  P06.canonicalP06AnimalConstantCertificate
    (PhysicalA1A2A3InfluenceInputs.p06ModelLeaf inputs)

finiteRootedInfluenceAssembly :
  ∀ {Scale Bound}
    {algebra : Influence.InfluenceAlgebra Bound} →
  (inputs : PhysicalA1A2A3InfluenceInputs algebra) →
  ∀ (scale : Scale) (cutoff : Nat) →
  Influence.InfluenceAlgebra.LessEqual algebra
    (Influence.partialSum algebra
      (Influence.OscillationAnimalShells.shellActivity
        (PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale))
      cutoff)
    (Influence.partialSum algebra
      (Influence.OscillationAnimalShells.shellMajorant
        (PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale))
      cutoff)
finiteRootedInfluenceAssembly inputs scale cutoff =
  Influence.rootedPartialActivityBelowMajorant
    (PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale)
    cutoff

canonicalUniformPolymerInfluence :
  ∀ {Scale Bound}
    {algebra : Influence.InfluenceAlgebra Bound} →
  PhysicalA1A2A3InfluenceInputs algebra →
  Influence.UniformPolymerInfluence Scale Bound algebra
canonicalUniformPolymerInfluence inputs = record
  { shellsAt = PhysicalA1A2A3InfluenceInputs.shellsAt inputs
  ; commonWeightedRatio =
      PhysicalA1A2A3InfluenceInputs.canonicalWeightedRatio inputs
  ; weightedRatioAtScale =
      PhysicalA1A2A3InfluenceInputs.weightedRatioAtScaleIsCanonical inputs
  ; StrictlyLess =
      PhysicalA1A2A3InfluenceInputs.StrictlyLess inputs
  ; one = PhysicalA1A2A3InfluenceInputs.one inputs
  ; commonWeightedRatioBelowOne =
      PhysicalA1A2A3InfluenceInputs.canonicalWeightedRatioBelowOne inputs
  }

record CanonicalA1A2A3InfluenceCertificate
    {Scale Bound : Set}
    (algebra : Influence.InfluenceAlgebra Bound) : Set₁ where
  field
    inputs : PhysicalA1A2A3InfluenceInputs algebra

    p06AnimalConstant :
      P06.CanonicalP06AnimalConstantCertificate
        (PhysicalA1A2A3InfluenceInputs.p06ModelLeaf inputs)

    uniformInfluence :
      Influence.UniformPolymerInfluence Scale Bound algebra

    finitePartialSumBound :
      ∀ (scale : Scale) (cutoff : Nat) →
      Influence.InfluenceAlgebra.LessEqual algebra
        (Influence.partialSum algebra
          (Influence.OscillationAnimalShells.shellActivity
            (PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale))
          cutoff)
        (Influence.partialSum algebra
          (Influence.OscillationAnimalShells.shellMajorant
            (PhysicalA1A2A3InfluenceInputs.shellsAt inputs scale))
          cutoff)

open CanonicalA1A2A3InfluenceCertificate public

canonicalA1A2A3InfluenceCertificate :
  ∀ {Scale Bound}
    {algebra : Influence.InfluenceAlgebra Bound} →
  (inputs : PhysicalA1A2A3InfluenceInputs algebra) →
  CanonicalA1A2A3InfluenceCertificate algebra
canonicalA1A2A3InfluenceCertificate inputs = record
  { inputs = inputs
  ; p06AnimalConstant = canonicalP06Certificate inputs
  ; uniformInfluence = canonicalUniformPolymerInfluence inputs
  ; finitePartialSumBound = finiteRootedInfluenceAssembly inputs
  }

p06A1A2A3FiniteInfluenceAssemblyLevel : ProofLevel
p06A1A2A3FiniteInfluenceAssemblyLevel = machineChecked

p06PhysicalA1A2A3InputsLevel : ProofLevel
p06PhysicalA1A2A3InputsLevel = conditional

recentA1A2A3AuditLeadAuthorityLevel : ProofLevel
recentA1A2A3AuditLeadAuthorityLevel = conjectural
