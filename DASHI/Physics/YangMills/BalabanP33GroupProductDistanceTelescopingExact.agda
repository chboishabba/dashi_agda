module DASHI.Physics.YangMills.BalabanP33GroupProductDistanceTelescopingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer (2015).
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- For equal-length ordered products in a group with a bi-invariant metric,
-- the distance between the products is at most the sum of the pointwise link
-- distances.  This is the exact noncommutative telescope needed to turn the
-- 48 literal Wilson cross-link occurrences into the rho/2 budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record BiInvariantMetricProductData : Set₁ where
  field
    Carrier Bound : Set
    unit : Carrier
    multiply : Carrier → Carrier → Carrier
    distance : Carrier → Carrier → Bound
    zeroBound : Bound
    addBound : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    lessEqualReflexive : ∀ value → LessEqual value value
    lessEqualTransitive : ∀ {a b c} →
      LessEqual a b → LessEqual b c → LessEqual a c
    addMonotone : ∀ {a b c d} →
      LessEqual a b → LessEqual c d →
      LessEqual (addBound a c) (addBound b d)

    selfDistanceZero : ∀ value →
      LessEqual (distance value value) zeroBound
    triangle : ∀ first middle last →
      LessEqual (distance first last)
        (addBound (distance first middle) (distance middle last))
    rightInvariant : ∀ first second right →
      distance (multiply first right) (multiply second right)
      ≡ distance first second
    leftInvariant : ∀ left first second →
      distance (multiply left first) (multiply left second)
      ≡ distance first second

open BiInvariantMetricProductData public

data PairedFactors (dataSet : BiInvariantMetricProductData) : Set where
  pairedNil : PairedFactors dataSet
  pairedCons :
    Carrier dataSet → Carrier dataSet → PairedFactors dataSet →
    PairedFactors dataSet

leftProduct :
  ∀ {dataSet} → PairedFactors dataSet → Carrier dataSet
leftProduct {dataSet} pairedNil = unit dataSet
leftProduct {dataSet} (pairedCons left right tail) =
  multiply dataSet left (leftProduct tail)

rightProduct :
  ∀ {dataSet} → PairedFactors dataSet → Carrier dataSet
rightProduct {dataSet} pairedNil = unit dataSet
rightProduct {dataSet} (pairedCons left right tail) =
  multiply dataSet right (rightProduct tail)

pointwiseDistanceSum :
  ∀ {dataSet} → PairedFactors dataSet → Bound dataSet
pointwiseDistanceSum {dataSet} pairedNil = zeroBound dataSet
pointwiseDistanceSum {dataSet} (pairedCons left right tail) =
  addBound dataSet
    (distance dataSet left right)
    (pointwiseDistanceSum tail)

productDistanceTelescoping :
  ∀ {dataSet} (factors : PairedFactors dataSet) →
  LessEqual dataSet
    (distance dataSet (leftProduct factors) (rightProduct factors))
    (pointwiseDistanceSum factors)
productDistanceTelescoping {dataSet} pairedNil =
  selfDistanceZero dataSet (unit dataSet)
productDistanceTelescoping {dataSet}
    (pairedCons left right tail) =
  let
    leftTail = leftProduct tail
    rightTail = rightProduct tail
    triangleBound =
      triangle dataSet
        (multiply dataSet left leftTail)
        (multiply dataSet right leftTail)
        (multiply dataSet right rightTail)
    invariantTriangle =
      subst
        (λ upper →
          LessEqual dataSet
            (distance dataSet
              (multiply dataSet left leftTail)
              (multiply dataSet right rightTail))
            upper)
        (cong₂ (addBound dataSet)
          (rightInvariant dataSet left right leftTail)
          (leftInvariant dataSet right leftTail rightTail))
        triangleBound
    tailBound = productDistanceTelescoping tail
    summedTail = addMonotone dataSet
      (lessEqualReflexive dataSet (distance dataSet left right))
      tailBound
  in
  lessEqualTransitive dataSet invariantTriangle summedTail

productDistanceTelescopeLevel : ProofLevel
productDistanceTelescopeLevel = machineChecked

physicalSU2MetricInstantiationLevel : ProofLevel
physicalSU2MetricInstantiationLevel = conditional
