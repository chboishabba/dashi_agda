module DASHI.Physics.YangMills.BalabanClayGate4ThreeWayRemainderDecompositionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact ownership split for the physical remainder.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization II: Localization, Exponentiation, and Bounds
-- for the R-Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The R-operation activity is only one contribution. It must not be identified
-- with the complete H-R_beta remainder. We separate the small-field integrated
-- fluctuation term, the localized R-operation term, and the boundary/hole term.
------------------------------------------------------------------------

record ThreeWayRemainderAlgebra (Remainder Bound : Set) : Set₁ where
  field
    addRemainder : Remainder → Remainder → Remainder
    addBound : Bound → Bound → Bound
    magnitude : Remainder → Bound
    LessEqual : Bound → Bound → Set

    threeTermTriangle : ∀ first second third →
      LessEqual
        (magnitude
          (addRemainder first (addRemainder second third)))
        (addBound (magnitude first)
          (addBound (magnitude second) (magnitude third)))

    addMonotone : ∀ {left leftUpper right rightUpper} →
      LessEqual left leftUpper → LessEqual right rightUpper →
      LessEqual (addBound left right) (addBound leftUpper rightUpper)

    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

open ThreeWayRemainderAlgebra public

record ThreeWayPhysicalRemainder
    {Remainder Bound : Set}
    (algebra : ThreeWayRemainderAlgebra Remainder Bound) : Set₁ where
  field
    total smallField rOperation boundary : Remainder

    totalMeaning :
      total
      ≡ addRemainder algebra smallField
          (addRemainder algebra rOperation boundary)

    smallFieldMajorant rOperationMajorant boundaryMajorant : Bound

    smallFieldBound :
      LessEqual algebra
        (magnitude algebra smallField) smallFieldMajorant
    rOperationBound :
      LessEqual algebra
        (magnitude algebra rOperation) rOperationMajorant
    boundaryBound :
      LessEqual algebra
        (magnitude algebra boundary) boundaryMajorant

open ThreeWayPhysicalRemainder public

threeWayRemainderBound :
  ∀ {Remainder Bound}
    {algebra : ThreeWayRemainderAlgebra Remainder Bound} →
  (dataSet : ThreeWayPhysicalRemainder algebra) →
  LessEqual algebra
    (magnitude algebra (total dataSet))
    (addBound algebra
      (smallFieldMajorant dataSet)
      (addBound algebra
        (rOperationMajorant dataSet)
        (boundaryMajorant dataSet)))
threeWayRemainderBound {algebra = algebra} dataSet =
  subst
    (λ selected → LessEqual algebra
      (magnitude algebra selected)
      (addBound algebra
        (smallFieldMajorant dataSet)
        (addBound algebra
          (rOperationMajorant dataSet)
          (boundaryMajorant dataSet))))
    (sym (totalMeaning dataSet))
    (transitive algebra
      (threeTermTriangle algebra
        (smallField dataSet)
        (rOperation dataSet)
        (boundary dataSet))
      (addMonotone algebra
        (smallFieldBound dataSet)
        (addMonotone algebra
          (rOperationBound dataSet)
          (boundaryBound dataSet))))

threeWayRemainderOwnershipLevel : ProofLevel
threeWayRemainderOwnershipLevel = machineChecked

threeWayRemainderMajorantAssemblyLevel : ProofLevel
threeWayRemainderMajorantAssemblyLevel = machineChecked

physicalSmallFieldIntegratedRemainderInputsLevel : ProofLevel
physicalSmallFieldIntegratedRemainderInputsLevel = conditional

physicalROperationRemainderInputsLevel : ProofLevel
physicalROperationRemainderInputsLevel = conditional

physicalBoundaryRemainderInputsLevel : ProofLevel
physicalBoundaryRemainderInputsLevel = conditional
