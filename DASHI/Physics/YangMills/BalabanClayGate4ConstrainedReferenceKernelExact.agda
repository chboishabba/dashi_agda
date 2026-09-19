module DASHI.Physics.YangMills.BalabanClayGate4ConstrainedReferenceKernelExact where

------------------------------------------------------------------------
-- CONSTRAINED GATE4 REFERENCE WEIGHT -> NORMALIZED FIBRE KERNEL
--
-- The T operation integrates fast variables at fixed slow field.  Therefore
-- the normalized reference object naturally used by finite RG reopening is a
-- conditional fibre law kappa(slow,fine), not a global fine marginal.
--
-- We construct it from the physical raw reference weight masked by the literal
-- P3 coarse constraint, then normalize that masked mass.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Finite
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceFactorAssemblyExact as Factor
import DASHI.Physics.YangMills.BalabanClayGate4FlatReferencePositiveWitnessExact as Flat
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass

record TypedReferenceCoarseConstraint
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) : Set₁ where
  field
    referenceCoarseConstraintExact :
      ∀ scale component slow →
      Integral.blockMap
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
        (Factor.referenceFine
          (Preferred.canonicalReferenceInputs
            referenceInputs scale component slow))
      ≡ slow

open TypedReferenceCoarseConstraint public

rawReference :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Scale → Component → SlowField → Fine → ℚ
rawReference referenceInputs =
  Flat.rawSelectedReference (Preferred.factors referenceInputs)

constrainedRawReference :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Scale → Component → SlowField → Fine → ℚ
constrainedRawReference {construction = construction}
  referenceInputs scale component slow fine =
  Integral.selectedWith
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    (rawReference referenceInputs scale component slow)
    slow fine

constrainedRawReferenceNonnegative :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    scale component slow fine →
  0ℚ ≤ constrainedRawReference
    referenceInputs scale component slow fine
constrainedRawReferenceNonnegative
  {construction = construction}
  referenceInputs scale component slow fine
  with Integral.coarseMatches
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    fine slow
... | true =
  Flat.selectedWeightNonnegative
    (Preferred.factors referenceInputs)
    scale component slow fine
... | false = ℚP.≤-refl

referenceWitnessMatches :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}} →
  TypedReferenceCoarseConstraint referenceInputs →
  ∀ scale component slow →
  Integral.coarseMatches
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    (Factor.referenceFine
      (Preferred.canonicalReferenceInputs
        referenceInputs scale component slow))
    slow
  ≡ true
referenceWitnessMatches
  {construction = construction}
  {referenceInputs = referenceInputs}
  typed scale component slow =
  Integral.coarseMatchesComplete
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    (Factor.referenceFine
      (Preferred.canonicalReferenceInputs
        referenceInputs scale component slow))
    slow
    (referenceCoarseConstraintExact typed scale component slow)

referenceWitnessConstrainedPositive :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (typed : TypedReferenceCoarseConstraint referenceInputs)
    scale component slow →
  Positive
    (constrainedRawReference referenceInputs scale component slow
      (Factor.referenceFine
        (Preferred.canonicalReferenceInputs
          referenceInputs scale component slow)))
referenceWitnessConstrainedPositive
  {referenceInputs = referenceInputs}
  typed scale component slow
  rewrite referenceWitnessMatches typed scale component slow =
  Flat.flatReferenceWeightPositive
    (Factor.asFlatReferenceInPhysicalFibre
      (Preferred.canonicalReferenceInputs
        referenceInputs scale component slow))

constrainedReferenceMass :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Scale → Component → SlowField → ℚ
constrainedReferenceMass {construction = construction}
  referenceInputs scale component slow =
  Sums.sumRational
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      scale component)
    (constrainedRawReference referenceInputs scale component slow)

constrainedReferenceMassPositive :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (typed : TypedReferenceCoarseConstraint referenceInputs)
    scale component slow →
  Positive
    (constrainedReferenceMass
      referenceInputs scale component slow)
constrainedReferenceMassPositive
  {construction = construction}
  {referenceInputs = referenceInputs}
  typed scale component slow =
  Finite.sumRationalPositiveAtMember
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      scale component)
    (constrainedRawReference referenceInputs scale component slow)
    (Factor.referenceFine
      (Preferred.canonicalReferenceInputs
        referenceInputs scale component slow))
    (Factor.referenceInFastFibre
      (Preferred.canonicalReferenceInputs
        referenceInputs scale component slow))
    (constrainedRawReferenceNonnegative
      referenceInputs scale component slow)
    (referenceWitnessConstrainedPositive
      typed scale component slow)

constrainedReferenceReciprocal :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Scale → Component → SlowField → ℚ
constrainedReferenceReciprocal referenceInputs scale component slow =
  Reciprocal.safeRationalReciprocal
    (constrainedReferenceMass referenceInputs scale component slow)

constrainedReferenceKernel :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}) →
  Scale → Component → SlowField → Fine → ℚ
constrainedReferenceKernel referenceInputs scale component slow fine =
  constrainedReferenceReciprocal referenceInputs scale component slow
  * constrainedRawReference referenceInputs scale component slow fine

constrainedReferenceKernelNormalized :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction}}
    (typed : TypedReferenceCoarseConstraint referenceInputs)
    scale component slow →
  Sums.sumRational
    (T.fastFibre
      (PhysicalT.canonicalPhysicalTData construction)
      scale component)
    (constrainedReferenceKernel referenceInputs scale component slow)
  ≡ 1ℚ
constrainedReferenceKernelNormalized
  {construction = construction}
  {referenceInputs = referenceInputs}
  typed scale component slow =
  trans
    (Sums.sumRationalScale
      (constrainedReferenceReciprocal
        referenceInputs scale component slow)
      (T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        scale component)
      (constrainedRawReference referenceInputs scale component slow))
    (Reciprocal.safeRationalReciprocalTimesPositive
      (constrainedReferenceMass referenceInputs scale component slow)
      (constrainedReferenceMassPositive
        typed scale component slow))

constrainedReferenceKernelOffFibreZero :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    scale component slow fine →
  (Integral.blockMap
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    fine
    ≡ slow → ⊥) →
  constrainedReferenceKernel referenceInputs
    scale component slow fine
  ≡ 0ℚ
constrainedReferenceKernelOffFibreZero
  {construction = construction}
  referenceInputs scale component slow fine noSupport
  with Integral.coarseMatches
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    fine slow
... | true =
  ⊥-elim
    (noSupport
      (Integral.coarseMatchesSound
        (T.sumData (PhysicalT.canonicalPhysicalTData construction))
        fine slow refl))
... | false =
  ℚRing.solve-∀
    (constrainedReferenceReciprocal
      referenceInputs scale component slow)

constrainedReferenceKernelLevel : ProofLevel
constrainedReferenceKernelLevel = machineChecked

constrainedReferenceKernelNormalizationLevel : ProofLevel
constrainedReferenceKernelNormalizationLevel = machineChecked

constrainedReferenceKernelSupportLevel : ProofLevel
constrainedReferenceKernelSupportLevel = machineChecked

typedCanonicalReferenceCoarseConstraintLevel : ProofLevel
typedCanonicalReferenceCoarseConstraintLevel = conditional
