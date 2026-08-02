module DASHI.Physics.YangMills.BalabanClayGate4OscillationAnimalInfluenceExact where

open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Per-link oscillation plus lattice-animal counting.
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
-- A physical source supplies an oscillation/activity estimate and an actual
-- rooted animal-count constant. The finite theorem below assembles every shell
-- estimate before any infinite geometric or polynomially weighted summability
-- theorem is invoked.
------------------------------------------------------------------------

record InfluenceAlgebra (Bound : Set) : Set₁ where
  field
    zero : Bound
    add multiply : Bound → Bound → Bound
    power : Bound → Nat → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (add left right) (add leftUpper rightUpper)

open InfluenceAlgebra public

partialSum :
  ∀ {Bound} → InfluenceAlgebra Bound → (Nat → Bound) → Nat → Bound
partialSum algebra term zero = zero algebra
partialSum algebra term (suc cutoff) =
  add algebra (partialSum algebra term cutoff) (term cutoff)

record OscillationAnimalShells
    {Scale Bound : Set}
    (algebra : InfluenceAlgebra Bound) : Set₁ where
  field
    scale : Scale
    shellActivity : Nat → Bound

    oscillationAmplitude irrelevanceFactor weightedRatio : Bound
    sizeWeight : Nat → Bound

    shellMajorant : Nat → Bound
    shellMajorantMeaning : ∀ size →
      shellMajorant size
      ≡ multiply algebra oscillationAmplitude
          (multiply algebra irrelevanceFactor
            (multiply algebra (sizeWeight size)
              (power algebra weightedRatio size)))

    shellBelowMajorant : ∀ size →
      LessEqual algebra (shellActivity size) (shellMajorant size)

open OscillationAnimalShells public

rootedPartialActivityBelowMajorant :
  ∀ {Scale Bound}
    {algebra : InfluenceAlgebra Bound} →
  (shells : OscillationAnimalShells {Scale} algebra) →
  ∀ cutoff →
  LessEqual algebra
    (partialSum algebra (shellActivity shells) cutoff)
    (partialSum algebra (shellMajorant shells) cutoff)
rootedPartialActivityBelowMajorant {algebra = algebra} shells zero =
  reflexive algebra (zero algebra)
rootedPartialActivityBelowMajorant {algebra = algebra} shells (suc cutoff) =
  addMonotone algebra
    (rootedPartialActivityBelowMajorant shells cutoff)
    (shellBelowMajorant shells cutoff)

record UniformPolymerInfluence
    (Scale Bound : Set)
    (algebra : InfluenceAlgebra Bound) : Set₁ where
  field
    shellsAt : Scale → OscillationAnimalShells {Scale} algebra
    commonWeightedRatio : Bound

    weightedRatioAtScale : ∀ scale →
      weightedRatio (shellsAt scale) ≡ commonWeightedRatio

    StrictlyLess : Bound → Bound → Set
    one : Bound
    commonWeightedRatioBelowOne :
      StrictlyLess commonWeightedRatio one

open UniformPolymerInfluence public

oscillationAnimalFiniteAssemblyLevel : ProofLevel
oscillationAnimalFiniteAssemblyLevel = machineChecked

physicalPerLinkOscillationInputsLevel : ProofLevel
physicalPerLinkOscillationInputsLevel = conditional

physicalAnimalCountConstantInputsLevel : ProofLevel
physicalAnimalCountConstantInputsLevel = conditional

physicalWeightedRatioSummabilityInputsLevel : ProofLevel
physicalWeightedRatioSummabilityInputsLevel = conditional
