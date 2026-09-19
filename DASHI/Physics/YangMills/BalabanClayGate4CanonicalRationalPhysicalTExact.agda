module DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact where

------------------------------------------------------------------------
-- PREFERRED PHYSICAL T CONSTRUCTION ON THE CANONICAL RATIONAL SUM
--
-- The historical PhysicalTConstruction accepts an arbitrary rational-valued
-- FiniteConstrainedSum, so its zero/add operations are not pinned.  This owner
-- keeps exactly the same physical fields but fixes the finite sum to the
-- canonical rational presentation from P3.
--
-- Consequently Gate4 reference normalization uses literal rational zero and
-- addition definitionally.  The only remaining scalar semantic weld is that
-- the abstract positive-cone Nonnegative predicate means ordinary rational
-- nonnegativity.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3CanonicalRationalConstrainedSumExact as RationalSum
import DASHI.Physics.YangMills.BalabanClayGate4PhysicalTDensityIdentificationExact as PhysicalT
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayT2LiteralWilsonSixFactorProducerExact as Six
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalReferenceNormalizationExact as Canonical
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceToFiniteRGProbabilityExact as Probability

record CanonicalRationalPhysicalTConstruction
    (Scale Fine SlowField Component Functional : Set) : Set₁ where
  field
    sumCarrier :
      RationalSum.CanonicalRationalConstrainedSumData Fine SlowField

    classData : T.ComponentClassData Scale Component

    Traversal : Set
    sixFactors : Six.LiteralWilsonSixFactorData Scale Traversal
    traversalOf : Component → SlowField → Fine → Traversal

    fastFibre : Scale → Component → List Fine
    evaluateFunctional : Functional → Fine → ℚ
    multiply : ℚ → ℚ → ℚ
    oneFunctional : Functional
    largeFieldIndicator : Scale → Component → Functional

open CanonicalRationalPhysicalTConstruction public

asPhysicalTConstruction :
  ∀ {Scale Fine SlowField Component Functional} →
  CanonicalRationalPhysicalTConstruction
    Scale Fine SlowField Component Functional →
  PhysicalT.PhysicalTConstruction
    Scale Fine SlowField Component Functional
asPhysicalTConstruction construction = record
  { sumData =
      RationalSum.canonicalRationalConstrainedSum
        (sumCarrier construction)
  ; classData = classData construction
  ; Traversal = Traversal construction
  ; sixFactors = sixFactors construction
  ; traversalOf = traversalOf construction
  ; fastFibre = fastFibre construction
  ; evaluateFunctional = evaluateFunctional construction
  ; multiply = multiply construction
  ; oneFunctional = oneFunctional construction
  ; largeFieldIndicator = largeFieldIndicator construction
  }

canonicalPhysicalTData :
  ∀ {Scale Fine SlowField Component Functional} →
  CanonicalRationalPhysicalTConstruction
    Scale Fine SlowField Component Functional →
  T.FiniteLocalTOperationData
    Scale Fine SlowField Component Functional ℚ
canonicalPhysicalTData construction =
  PhysicalT.physicalTData (asPhysicalTConstruction construction)

record RationalReferenceConeMeaning
    {Scale Fine SlowField Component Functional : Set}
    {construction :
      CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    (canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional
        (canonicalPhysicalTData construction)) : Set₁ where
  field
    nonnegativeMeansRationalNonnegative : ∀ {value} →
      PositiveMass.Nonnegative
        (Canonical.positiveAlgebra canonical) value →
      0ℚ ≤ value

open RationalReferenceConeMeaning public

canonicalRationalReferenceFoldSemantics :
  ∀ {Scale Fine SlowField Component Functional}
    {construction :
      CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional}
    {canonical :
      Canonical.CanonicalRationalReferenceNormalizationData
        Scale Fine SlowField Component Functional
        (canonicalPhysicalTData construction)} →
  RationalReferenceConeMeaning canonical →
  Probability.RationalReferenceFoldSemantics canonical
canonicalRationalReferenceFoldSemantics cone = record
  { zeroMeaning = Agda.Builtin.Equality.refl
  ; addMeaning = λ left right → Agda.Builtin.Equality.refl
  ; nonnegativeMeaning =
      nonnegativeMeansRationalNonnegative cone
  }

canonicalRationalPhysicalTConstructionLevel : ProofLevel
canonicalRationalPhysicalTConstructionLevel = machineChecked

canonicalRationalReferenceFoldArithmeticLevel : ProofLevel
canonicalRationalReferenceFoldArithmeticLevel = machineChecked

rationalReferenceConeMeaningLevel : ProofLevel
rationalReferenceConeMeaningLevel = conditional
