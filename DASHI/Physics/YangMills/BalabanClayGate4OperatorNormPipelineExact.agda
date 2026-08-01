module DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Operator-norm pipeline for a physical CMP109 derivative entry.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press (2012).
-- DOI: 10.1017/CBO9781139020411.
--
-- The physical entry estimate is assembled from four reusable stages:
--
--   path derivative -> transport -> dexp^{-1}/log -> outer dexp.
--
-- Submultiplicativity proves that the product of the four stage bounds is one
-- valid entry bound M.  The exact 128-row and 8-column Schur envelopes can then
-- consume M without introducing a fifth joint estimate.
------------------------------------------------------------------------

record OperatorNormAlgebra
    (Operator Bound : Set) : Set₁ where
  field
    compose : Operator → Operator → Operator
    operatorNorm : Operator → Bound

    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    multiplyMonotone : ∀ {left lower right upper} →
      LessEqual left lower → LessEqual right upper →
      LessEqual (multiply left right) (multiply lower upper)

    multiplyAssociative : ∀ left middle right →
      multiply (multiply left middle) right
      ≡ multiply left (multiply middle right)

    normSubmultiplicative : ∀ outer inner →
      LessEqual
        (operatorNorm (compose outer inner))
        (multiply (operatorNorm outer) (operatorNorm inner))

open OperatorNormAlgebra public

threeStageComposition :
  ∀ {Operator Bound} →
  OperatorNormAlgebra Operator Bound →
  Operator → Operator → Operator → Operator
threeStageComposition algebra outer middle inner =
  compose algebra outer (compose algebra middle inner)

fourStageComposition :
  ∀ {Operator Bound} →
  OperatorNormAlgebra Operator Bound →
  Operator → Operator → Operator → Operator → Operator
fourStageComposition algebra outer middle transport path =
  compose algebra outer
    (threeStageComposition algebra middle transport path)

threeStageNormBound :
  ∀ {Operator Bound}
    (algebra : OperatorNormAlgebra Operator Bound)
    outer middle inner outerBound middleBound innerBound →
  LessEqual algebra (operatorNorm algebra outer) outerBound →
  LessEqual algebra (operatorNorm algebra middle) middleBound →
  LessEqual algebra (operatorNorm algebra inner) innerBound →
  LessEqual algebra
    (operatorNorm algebra
      (threeStageComposition algebra outer middle inner))
    (multiply algebra outerBound
      (multiply algebra middleBound innerBound))
threeStageNormBound algebra outer middle inner outerBound middleBound innerBound
    outerEstimate middleEstimate innerEstimate =
  transitive algebra
    (normSubmultiplicative algebra outer
      (compose algebra middle inner))
    (multiplyMonotone algebra
      outerEstimate
      (transitive algebra
        (normSubmultiplicative algebra middle inner)
        (multiplyMonotone algebra middleEstimate innerEstimate)))

fourStageNormBound :
  ∀ {Operator Bound}
    (algebra : OperatorNormAlgebra Operator Bound)
    outer logarithm transport path
    outerBound logarithmBound transportBound pathBound →
  LessEqual algebra (operatorNorm algebra outer) outerBound →
  LessEqual algebra (operatorNorm algebra logarithm) logarithmBound →
  LessEqual algebra (operatorNorm algebra transport) transportBound →
  LessEqual algebra (operatorNorm algebra path) pathBound →
  LessEqual algebra
    (operatorNorm algebra
      (fourStageComposition algebra outer logarithm transport path))
    (multiply algebra outerBound
      (multiply algebra logarithmBound
        (multiply algebra transportBound pathBound)))
fourStageNormBound algebra outer logarithm transport path
    outerBound logarithmBound transportBound pathBound
    outerEstimate logarithmEstimate transportEstimate pathEstimate =
  transitive algebra
    (normSubmultiplicative algebra outer
      (threeStageComposition algebra logarithm transport path))
    (multiplyMonotone algebra
      outerEstimate
      (threeStageNormBound algebra logarithm transport path
        logarithmBound transportBound pathBound
        logarithmEstimate transportEstimate pathEstimate))

record CMP109DerivativeEntryPipeline
    (Operator Bound : Set) : Set₁ where
  field
    algebra : OperatorNormAlgebra Operator Bound

    outerDexp logarithmDexpInverse transportDerivative pathDerivative :
      Operator

    outerBound logarithmBound transportBound pathBound entryBound : Bound

    outerEstimate :
      LessEqual algebra (operatorNorm algebra outerDexp) outerBound
    logarithmEstimate :
      LessEqual algebra
        (operatorNorm algebra logarithmDexpInverse) logarithmBound
    transportEstimate :
      LessEqual algebra
        (operatorNorm algebra transportDerivative) transportBound
    pathEstimate :
      LessEqual algebra (operatorNorm algebra pathDerivative) pathBound

    entryBoundMeaning :
      entryBound
      ≡ multiply algebra outerBound
          (multiply algebra logarithmBound
            (multiply algebra transportBound pathBound))

open CMP109DerivativeEntryPipeline public

assembledDerivativeEntryOperator :
  ∀ {Operator Bound} →
  CMP109DerivativeEntryPipeline Operator Bound → Operator
assembledDerivativeEntryOperator pipeline =
  fourStageComposition (algebra pipeline)
    (outerDexp pipeline)
    (logarithmDexpInverse pipeline)
    (transportDerivative pipeline)
    (pathDerivative pipeline)

assembledDerivativeEntryNormBound :
  ∀ {Operator Bound}
    (pipeline : CMP109DerivativeEntryPipeline Operator Bound) →
  LessEqual (algebra pipeline)
    (operatorNorm (algebra pipeline)
      (assembledDerivativeEntryOperator pipeline))
    (entryBound pipeline)
assembledDerivativeEntryNormBound pipeline =
  subst
    (λ upper →
      LessEqual (algebra pipeline)
        (operatorNorm (algebra pipeline)
          (assembledDerivativeEntryOperator pipeline)) upper)
    (sym (entryBoundMeaning pipeline))
    (fourStageNormBound (algebra pipeline)
      (outerDexp pipeline)
      (logarithmDexpInverse pipeline)
      (transportDerivative pipeline)
      (pathDerivative pipeline)
      (outerBound pipeline)
      (logarithmBound pipeline)
      (transportBound pipeline)
      (pathBound pipeline)
      (outerEstimate pipeline)
      (logarithmEstimate pipeline)
      (transportEstimate pipeline)
      (pathEstimate pipeline))

operatorNormThreeStagePipelineLevel : ProofLevel
operatorNormThreeStagePipelineLevel = machineChecked

operatorNormFourStagePipelineLevel : ProofLevel
operatorNormFourStagePipelineLevel = machineChecked

cmp109EntryBoundProductAssemblyLevel : ProofLevel
cmp109EntryBoundProductAssemblyLevel = machineChecked

physicalOuterDexpNormInputsLevel : ProofLevel
physicalOuterDexpNormInputsLevel = conditional

physicalLogDexpInverseNormInputsLevel : ProofLevel
physicalLogDexpInverseNormInputsLevel = conditional

physicalTransportAndPathNormInputsLevel : ProofLevel
physicalTransportAndPathNormInputsLevel = conditional
