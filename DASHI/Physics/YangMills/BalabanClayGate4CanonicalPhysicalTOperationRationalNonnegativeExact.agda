module DASHI.Physics.YangMills.BalabanClayGate4CanonicalPhysicalTOperationRationalNonnegativeExact where

------------------------------------------------------------------------
-- CANONICAL RATIONAL PHYSICAL T-OPERATION AT 1 IS NONNEGATIVE
--
-- This avoids the abstract T-order entirely.
--
-- On the canonical rational constrained sum:
--   * each selected one-integrand is either 0 or the physical Wilson activity;
--   * the older physical activity carrier proves activity >= 0;
--   * the constrained fold is the literal rational sum.
--
-- Hence the selected physical T-operation at the unit observable is a
-- nonnegative rational scalar.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayT2WilsonActivityFactorProductExact as Factors
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4PreferredRationalReferenceNormalizationExact as Preferred
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Gate4
import DASHI.Physics.YangMills.BalabanClayGate4TPointwiseSixFactorComparisonExact as Relative

sumRationalNonnegative :
  ∀ {A : Set} (values : List A) (term : A → ℚ) →
  (∀ value → 0ℚ ≤ term value) →
  0ℚ ≤ Sums.sumRational values term
sumRationalNonnegative [] term pointwise = ℚP.≤-refl
sumRationalNonnegative (value ∷ values) term pointwise =
  ℚP.+-mono-≤
    (pointwise value)
    (sumRationalNonnegative values term pointwise)

selectedPhysicalOneIntegrandRationalNonnegative :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {comparison : Relative.RelativeSixFactorComparison Scale Traversal}
    (meaning :
      Relative.RelativeTPointwiseMeaning
        (PhysicalT.canonicalPhysicalTData construction)
        comparison)
    scale component slow fine →
  0ℚ ≤
    Integral.selectedWith
      (T.sumData (PhysicalT.canonicalPhysicalTData construction))
      (T.localIntegrand
        (PhysicalT.canonicalPhysicalTData construction)
        scale component slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction)))
      slow fine
selectedPhysicalOneIntegrandRationalNonnegative
  {construction = construction}
  {comparison = comparison}
  meaning scale component slow fine
  with Integral.coarseMatches
    (T.sumData (PhysicalT.canonicalPhysicalTData construction))
    fine slow
... | false = ℚP.≤-refl
... | true =
  subst
    (λ value → 0ℚ ≤ value)
    (sym (Relative.oneIntegrandMeaning
      meaning scale component slow fine))
    (Factors.activityNonnegative
      (Relative.physical comparison)
      scale
      (Relative.traversalOf meaning scale component slow fine))

canonicalPhysicalTOperationAtOneRationalNonnegative :
  ∀ {Scale Fine SlowField Component Functional Traversal}
    {construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (referenceInputs :
      Preferred.PreferredRationalReferenceNormalizationInputs
        {construction = construction})
    {comparison : Relative.RelativeSixFactorComparison Scale Traversal}
    (meaning :
      Relative.RelativeTPointwiseMeaning
        (PhysicalT.canonicalPhysicalTData construction)
        comparison)
    scale
    (selected :
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        scale)
    slow →
  0ℚ ≤
    T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData construction)
      scale selected slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData construction))
canonicalPhysicalTOperationAtOneRationalNonnegative
  {construction = construction}
  referenceInputs meaning scale selected slow =
  let
    tData = PhysicalT.canonicalPhysicalTData construction

    selector =
      Integral.selectedWith
        (T.sumData tData)
        (T.localIntegrand tData scale
          (T.component selected) slow
          (T.oneFunctional tData))
        slow

    fields = T.fastFibre tData scale (T.component selected)

    foldIsRationalSum =
      Gate4.foldSelectedIsRationalSum
        (Preferred.preferredRationalReferenceFoldSemantics referenceInputs)
        selector
        slow
        fields

    rationalSumNonnegative :
      0ℚ ≤ Sums.sumRational fields selector
    rationalSumNonnegative =
      sumRationalNonnegative fields selector
        (selectedPhysicalOneIntegrandRationalNonnegative
          meaning scale (T.component selected) slow)
  in
  subst
    (λ value → 0ℚ ≤ value)
    (sym foldIsRationalSum)
    rationalSumNonnegative

canonicalPhysicalTOperationRationalNonnegativeLevel : ProofLevel
canonicalPhysicalTOperationRationalNonnegativeLevel = machineChecked
