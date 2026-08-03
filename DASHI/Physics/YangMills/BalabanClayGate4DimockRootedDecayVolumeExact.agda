module DASHI.Physics.YangMills.BalabanClayGate4DimockRootedDecayVolumeExact where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Rooted decay sums imply a volume bound.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban - III. Convergence",
-- arXiv:1304.0705v1 [math-ph]. No DOI recorded.
--
-- Roman Kotecký and David Preiss,
-- "Cluster Expansion for Abstract Polymer Models",
-- Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762.
--
-- Dimock's final stability estimate uses the standard rooted-polymer step:
-- sum the exponentially decaying activities containing each block, and then
-- sum over the possible roots.  This module proves the finite order-theoretic
-- assembly.  The gauge-specific work is reduced to a rooted decay estimate and
-- an exact identification of the root budget with physical volume.
------------------------------------------------------------------------

record RootedDecayAlgebra (Scalar : Set) : Set₁ where
  field
    zero : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)

open RootedDecayAlgebra public

mapList : ∀ {A B : Set} → (A → B) → List A → List B
mapList function [] = []
mapList function (value ∷ values) =
  function value ∷ mapList function values

finiteSum :
  ∀ {Scalar} → RootedDecayAlgebra Scalar → List Scalar → Scalar
finiteSum algebra [] = zero algebra
finiteSum algebra (value ∷ values) =
  add algebra value (finiteSum algebra values)

finiteSumPointwiseMonotone :
  ∀ {A Scalar}
    (algebra : RootedDecayAlgebra Scalar)
    (lower upper : A → Scalar)
    values →
  (∀ value → LessEqual algebra (lower value) (upper value)) →
  LessEqual algebra
    (finiteSum algebra (mapList lower values))
    (finiteSum algebra (mapList upper values))
finiteSumPointwiseMonotone algebra lower upper [] estimate =
  reflexive algebra (zero algebra)
finiteSumPointwiseMonotone algebra lower upper (value ∷ values) estimate =
  addMonotone algebra
    (estimate value)
    (finiteSumPointwiseMonotone
      algebra lower upper values estimate)

record RootedDecayVolumeData
    (Root Polymer Scalar : Set) : Set₁ where
  field
    algebra : RootedDecayAlgebra Scalar
    roots : List Root
    polymersAt : Root → List Polymer
    decayWeight : Polymer → Scalar
    rootBudget : Root → Scalar
    volume : Scalar

    rootedDecayBound : ∀ root →
      LessEqual algebra
        (finiteSum algebra
          (mapList decayWeight (polymersAt root)))
        (rootBudget root)

    rootBudgetsBelowVolume :
      LessEqual algebra
        (finiteSum algebra (mapList rootBudget roots))
        volume

  rootedDecaySum : Scalar
  rootedDecaySum =
    finiteSum algebra
      (mapList
        (λ root →
          finiteSum algebra
            (mapList decayWeight (polymersAt root)))
        roots)

open RootedDecayVolumeData public

rootedDecaySumBelowVolume :
  ∀ {Root Polymer Scalar}
    (dataSet : RootedDecayVolumeData Root Polymer Scalar) →
  LessEqual (algebra dataSet)
    (rootedDecaySum dataSet)
    (volume dataSet)
rootedDecaySumBelowVolume dataSet =
  transitive (algebra dataSet)
    (finiteSumPointwiseMonotone
      (algebra dataSet)
      (λ root →
        finiteSum (algebra dataSet)
          (mapList (decayWeight dataSet)
            (polymersAt dataSet root)))
      (rootBudget dataSet)
      (roots dataSet)
      (rootedDecayBound dataSet))
    (rootBudgetsBelowVolume dataSet)

record PhysicalDecayEnumerationIdentification
    {Root Polymer Scalar : Set}
    (rooted : RootedDecayVolumeData Root Polymer Scalar) : Set₁ where
  field
    physicalAllPolymerDecaySum : Scalar
    physicalAllPolymerDecaySumMeaning :
      physicalAllPolymerDecaySum ≡ rootedDecaySum rooted

open PhysicalDecayEnumerationIdentification public

physicalAllPolymerDecaySumBelowVolume :
  ∀ {Root Polymer Scalar}
    {rooted : RootedDecayVolumeData Root Polymer Scalar} →
  (identification : PhysicalDecayEnumerationIdentification rooted) →
  LessEqual (algebra rooted)
    (physicalAllPolymerDecaySum identification)
    (volume rooted)
physicalAllPolymerDecaySumBelowVolume {rooted = rooted} identification
  rewrite physicalAllPolymerDecaySumMeaning identification =
  rootedDecaySumBelowVolume rooted

dimockRootedDecayFiniteAssemblyLevel : ProofLevel
dimockRootedDecayFiniteAssemblyLevel = machineChecked

dimockRootedDecayVolumeSourceLevel : ProofLevel
dimockRootedDecayVolumeSourceLevel = standardImported

physicalYangMillsRootedPolymerEnumerationInputsLevel : ProofLevel
physicalYangMillsRootedPolymerEnumerationInputsLevel = conditional

physicalYangMillsRootedDecayEstimateInputsLevel : ProofLevel
physicalYangMillsRootedDecayEstimateInputsLevel = conditional
