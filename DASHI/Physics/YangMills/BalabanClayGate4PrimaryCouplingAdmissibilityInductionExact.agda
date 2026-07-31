module DASHI.Physics.YangMills.BalabanClayGate4PrimaryCouplingAdmissibilityInductionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- All-scale admissibility and quantitative inverse-coupling growth.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- J. Dimock,
-- "The Renormalization Group According to Balaban, I. Small Fields",
-- Reviews in Mathematical Physics 25 (2013), 1330010.
-- DOI: 10.1142/S0129055X13300100; arXiv:1108.1335.
--
-- The induction is elementary. The physical input remains the one-step
-- beta/remainder estimate preserving the selected admissible interval.
------------------------------------------------------------------------

record PrimaryCouplingAdmissibilityInduction
    (Coupling : Set) : Set₁ where
  field
    coupling : Nat → Coupling
    Admissible : Coupling → Set
    initialCouplingAdmissible : Admissible (coupling zero)
    oneStepCouplingPreservesAdmissibility : ∀ count →
      Admissible (coupling count) → Admissible (coupling (suc count))

open PrimaryCouplingAdmissibilityInduction public

allScalesCouplingAdmissible :
  ∀ {Coupling}
    (dataSet : PrimaryCouplingAdmissibilityInduction Coupling)
    count → Admissible dataSet (coupling dataSet count)
allScalesCouplingAdmissible dataSet zero =
  initialCouplingAdmissible dataSet
allScalesCouplingAdmissible dataSet (suc count) =
  oneStepCouplingPreservesAdmissibility dataSet count
    (allScalesCouplingAdmissible dataSet count)

record OrderedAdditiveFlow (Scalar : Set) : Set₁ where
  field
    zeroScalar : Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right
    addMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (add left right) (add lower upper)
    addZeroRight : ∀ value → add value zeroScalar ≡ value
    addAssociative : ∀ left middle right →
      add (add left middle) right ≡ add left (add middle right)

open OrderedAdditiveFlow public

natScale :
  ∀ {Scalar} → OrderedAdditiveFlow Scalar → Nat → Scalar → Scalar
natScale algebra zero value = zeroScalar algebra
natScale algebra (suc count) value =
  add algebra (natScale algebra count value) value

record QuantitativeInverseCouplingFlow (Scalar : Set) : Set₁ where
  field
    algebra : OrderedAdditiveFlow Scalar
    inverseCoupling : Nat → Scalar
    betaLower : Scalar
    oneStepInverseCouplingLowerBound : ∀ count →
      LessEqual algebra
        (add algebra (inverseCoupling count) betaLower)
        (inverseCoupling (suc count))

open QuantitativeInverseCouplingFlow public

inverseCouplingLinearEnvelope :
  ∀ {Scalar} → QuantitativeInverseCouplingFlow Scalar → Nat → Scalar
inverseCouplingLinearEnvelope dataSet count =
  add (algebra dataSet)
    (inverseCoupling dataSet zero)
    (natScale (algebra dataSet) count (betaLower dataSet))

inverseCouplingLinearLowerBound :
  ∀ {Scalar}
    (dataSet : QuantitativeInverseCouplingFlow Scalar)
    count →
  LessEqual (algebra dataSet)
    (inverseCouplingLinearEnvelope dataSet count)
    (inverseCoupling dataSet count)
inverseCouplingLinearLowerBound dataSet zero =
  subst
    (λ lower → LessEqual (algebra dataSet) lower
      (inverseCoupling dataSet zero))
    (sym (addZeroRight (algebra dataSet)
      (inverseCoupling dataSet zero)))
    (reflexive (algebra dataSet) (inverseCoupling dataSet zero))
inverseCouplingLinearLowerBound dataSet (suc count) =
  transitive (algebra dataSet)
    (subst
      (λ lower → LessEqual (algebra dataSet) lower
        (add (algebra dataSet)
          (inverseCoupling dataSet count)
          (betaLower dataSet)))
      (addAssociative (algebra dataSet)
        (inverseCoupling dataSet zero)
        (natScale (algebra dataSet) count (betaLower dataSet))
        (betaLower dataSet))
      (addMonotone (algebra dataSet)
        (inverseCouplingLinearLowerBound dataSet count)
        (reflexive (algebra dataSet) (betaLower dataSet))))
    (oneStepInverseCouplingLowerBound dataSet count)

record HRBetaRemainderDominance
    (Scale Scalar : Set) : Set₁ where
  field
    inverseCoupling : Scale → Scalar
    nextScale : Scale → Scale
    leadingIncrement remainder netIncrement betaLower : Scale → Scalar
    add : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    netIncrementMeaning : ∀ scale →
      netIncrement scale ≡ add (leadingIncrement scale) (remainder scale)
    oneStepMeaning : ∀ scale →
      inverseCoupling (nextScale scale)
      ≡ add (inverseCoupling scale) (netIncrement scale)
    betaDominatesRemainder : ∀ scale →
      LessEqual (betaLower scale) (netIncrement scale)
    addMonotoneLeft : ∀ {lower upper} common →
      LessEqual lower upper → LessEqual (add common lower) (add common upper)

open HRBetaRemainderDominance public

inverseCouplingGrowsByBetaLower :
  ∀ {Scale Scalar}
    (dataSet : HRBetaRemainderDominance Scale Scalar)
    scale →
  LessEqual dataSet
    (add dataSet
      (inverseCoupling dataSet scale)
      (betaLower dataSet scale))
    (inverseCoupling dataSet (nextScale dataSet scale))
inverseCouplingGrowsByBetaLower dataSet scale =
  subst
    (λ upper → LessEqual dataSet
      (add dataSet
        (inverseCoupling dataSet scale)
        (betaLower dataSet scale)) upper)
    (sym (oneStepMeaning dataSet scale))
    (addMonotoneLeft dataSet
      (inverseCoupling dataSet scale)
      (betaDominatesRemainder dataSet scale))

allScaleAdmissibilityInductionLevel : ProofLevel
allScaleAdmissibilityInductionLevel = machineChecked

inverseCouplingLinearLowerBoundLevel : ProofLevel
inverseCouplingLinearLowerBoundLevel = machineChecked

betaRemainderDominanceStepLevel : ProofLevel
betaRemainderDominanceStepLevel = machineChecked

balabanPrimaryFlowProvenanceLevel : ProofLevel
balabanPrimaryFlowProvenanceLevel = standardImported

dimockAdmissibilityMethodologyLevel : ProofLevel
dimockAdmissibilityMethodologyLevel = standardImported

physicalBetaRemainderDominanceInputsLevel : ProofLevel
physicalBetaRemainderDominanceInputsLevel = conditional

physicalOneStepAdmissibilityInputsLevel : ProofLevel
physicalOneStepAdmissibilityInputsLevel = conditional

physicalPositiveUniformBetaLowerInputsLevel : ProofLevel
physicalPositiveUniformBetaLowerInputsLevel = conditional
