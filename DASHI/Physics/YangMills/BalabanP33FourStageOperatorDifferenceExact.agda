module DASHI.Physics.YangMills.BalabanP33FourStageOperatorDifferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics, 1995 reprint.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- Roger A. Horn and Charles R. Johnson,
-- "Matrix Analysis", second edition, Cambridge University Press, 2012.
-- DOI: 10.1017/CBO9781139020411.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- DASHI CONTRIBUTION
--
-- The CMP109 derivative entry is a four-stage composition
--
--   outer dexp o inverse-dexp(log) o transport derivative o path derivative.
--
-- This module proves the exact noncommutative telescoping identity for the
-- difference between the background and reference four-stage operators, then
-- proves the corresponding norm estimate.  Consequently ||DQ_A-DQ_0|| reduces
-- to four separately auditable stage differences rather than a joint physical
-- operator estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4OperatorNormPipelineExact as Pipeline

record AdditiveOperatorNormAlgebra
    (Operator Bound : Set) : Set₁ where
  field
    normAlgebra : Pipeline.OperatorNormAlgebra Operator Bound

    zeroOperator : Operator
    addOperator subtractOperator : Operator → Operator → Operator

    zeroBound : Bound
    addBound : Bound → Bound → Bound

    subtractChain : ∀ left middle right →
      subtractOperator left right
      ≡ addOperator
          (subtractOperator left middle)
          (subtractOperator middle right)

    subtractComposedOuter : ∀ left right inner →
      subtractOperator
        (Pipeline.compose normAlgebra left inner)
        (Pipeline.compose normAlgebra right inner)
      ≡ Pipeline.compose normAlgebra
          (subtractOperator left right) inner

    subtractComposedInner : ∀ outer left right →
      subtractOperator
        (Pipeline.compose normAlgebra outer left)
        (Pipeline.compose normAlgebra outer right)
      ≡ Pipeline.compose normAlgebra outer
          (subtractOperator left right)

    normAddTriangle : ∀ left right →
      Pipeline.LessEqual normAlgebra
        (Pipeline.operatorNorm normAlgebra
          (addOperator left right))
        (addBound
          (Pipeline.operatorNorm normAlgebra left)
          (Pipeline.operatorNorm normAlgebra right))

    addBoundMonotone : ∀ {left lower right upper} →
      Pipeline.LessEqual normAlgebra left lower →
      Pipeline.LessEqual normAlgebra right upper →
      Pipeline.LessEqual normAlgebra
        (addBound left right) (addBound lower upper)

open AdditiveOperatorNormAlgebra public

record FourStageBackgroundPair
    (Operator Bound : Set)
    (algebra : AdditiveOperatorNormAlgebra Operator Bound) : Set₁ where
  field
    backgroundOuter backgroundLogarithm
      backgroundTransport backgroundPath : Operator
    referenceOuter referenceLogarithm
      referenceTransport referencePath : Operator

open FourStageBackgroundPair public

backgroundFourStage :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
backgroundFourStage {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (backgroundOuter pair)
    (backgroundLogarithm pair)
    (backgroundTransport pair)
    (backgroundPath pair)

referenceFourStage :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
referenceFourStage {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (referenceTransport pair)
    (referencePath pair)

intermediateOne :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
intermediateOne {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (backgroundLogarithm pair)
    (backgroundTransport pair)
    (backgroundPath pair)

intermediateTwo :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
intermediateTwo {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (backgroundTransport pair)
    (backgroundPath pair)

intermediateThree :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
intermediateThree {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (referenceTransport pair)
    (backgroundPath pair)

outerDifferenceTerm :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
outerDifferenceTerm {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (subtractOperator algebra
      (backgroundOuter pair) (referenceOuter pair))
    (backgroundLogarithm pair)
    (backgroundTransport pair)
    (backgroundPath pair)

logarithmDifferenceTerm :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
logarithmDifferenceTerm {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (subtractOperator algebra
      (backgroundLogarithm pair) (referenceLogarithm pair))
    (backgroundTransport pair)
    (backgroundPath pair)

transportDifferenceTerm :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
transportDifferenceTerm {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (subtractOperator algebra
      (backgroundTransport pair) (referenceTransport pair))
    (backgroundPath pair)

pathDifferenceTerm :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
pathDifferenceTerm {algebra = algebra} pair =
  Pipeline.fourStageComposition (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (referenceTransport pair)
    (subtractOperator algebra
      (backgroundPath pair) (referencePath pair))

fourDifferenceTermSum :
  ∀ {Operator Bound algebra} →
  FourStageBackgroundPair Operator Bound algebra → Operator
fourDifferenceTermSum {algebra = algebra} pair =
  addOperator algebra (outerDifferenceTerm pair)
    (addOperator algebra (logarithmDifferenceTerm pair)
      (addOperator algebra
        (transportDifferenceTerm pair)
        (pathDifferenceTerm pair)))

fourStageDifferenceTelescope :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (backgroundFourStage pair) (referenceFourStage pair)
  ≡ addOperator algebra
      (subtractOperator algebra
        (backgroundFourStage pair) (intermediateOne pair))
      (addOperator algebra
        (subtractOperator algebra
          (intermediateOne pair) (intermediateTwo pair))
        (addOperator algebra
          (subtractOperator algebra
            (intermediateTwo pair) (intermediateThree pair))
          (subtractOperator algebra
            (intermediateThree pair) (referenceFourStage pair))))
fourStageDifferenceTelescope algebra pair =
  trans
    (subtractChain algebra
      (backgroundFourStage pair)
      (intermediateOne pair)
      (referenceFourStage pair))
    (cong
      (addOperator algebra
        (subtractOperator algebra
          (backgroundFourStage pair) (intermediateOne pair)))
      (trans
        (subtractChain algebra
          (intermediateOne pair)
          (intermediateTwo pair)
          (referenceFourStage pair))
        (cong
          (addOperator algebra
            (subtractOperator algebra
              (intermediateOne pair) (intermediateTwo pair)))
          (subtractChain algebra
            (intermediateTwo pair)
            (intermediateThree pair)
            (referenceFourStage pair)))))

outerDifferenceFactorization :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (backgroundFourStage pair) (intermediateOne pair)
  ≡ outerDifferenceTerm pair
outerDifferenceFactorization algebra pair =
  subtractComposedOuter algebra
    (backgroundOuter pair)
    (referenceOuter pair)
    (Pipeline.threeStageComposition (normAlgebra algebra)
      (backgroundLogarithm pair)
      (backgroundTransport pair)
      (backgroundPath pair))

logarithmDifferenceFactorization :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (intermediateOne pair) (intermediateTwo pair)
  ≡ logarithmDifferenceTerm pair
logarithmDifferenceFactorization algebra pair =
  trans
    (subtractComposedInner algebra
      (referenceOuter pair)
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (backgroundLogarithm pair)
        (backgroundTransport pair)
        (backgroundPath pair))
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (referenceLogarithm pair)
        (backgroundTransport pair)
        (backgroundPath pair)))
    (cong (Pipeline.compose (normAlgebra algebra) (referenceOuter pair))
      (subtractComposedOuter algebra
        (backgroundLogarithm pair)
        (referenceLogarithm pair)
        (Pipeline.compose (normAlgebra algebra)
          (backgroundTransport pair) (backgroundPath pair))))

transportDifferenceFactorization :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (intermediateTwo pair) (intermediateThree pair)
  ≡ transportDifferenceTerm pair
transportDifferenceFactorization algebra pair =
  trans
    (subtractComposedInner algebra
      (referenceOuter pair)
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (referenceLogarithm pair)
        (backgroundTransport pair)
        (backgroundPath pair))
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (referenceLogarithm pair)
        (referenceTransport pair)
        (backgroundPath pair)))
    (cong (Pipeline.compose (normAlgebra algebra) (referenceOuter pair))
      (trans
        (subtractComposedInner algebra
          (referenceLogarithm pair)
          (Pipeline.compose (normAlgebra algebra)
            (backgroundTransport pair) (backgroundPath pair))
          (Pipeline.compose (normAlgebra algebra)
            (referenceTransport pair) (backgroundPath pair)))
        (cong
          (Pipeline.compose (normAlgebra algebra) (referenceLogarithm pair))
          (subtractComposedOuter algebra
            (backgroundTransport pair)
            (referenceTransport pair)
            (backgroundPath pair)))))

pathDifferenceFactorization :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (intermediateThree pair) (referenceFourStage pair)
  ≡ pathDifferenceTerm pair
pathDifferenceFactorization algebra pair =
  trans
    (subtractComposedInner algebra
      (referenceOuter pair)
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (referenceLogarithm pair)
        (referenceTransport pair)
        (backgroundPath pair))
      (Pipeline.threeStageComposition (normAlgebra algebra)
        (referenceLogarithm pair)
        (referenceTransport pair)
        (referencePath pair)))
    (cong (Pipeline.compose (normAlgebra algebra) (referenceOuter pair))
      (trans
        (subtractComposedInner algebra
          (referenceLogarithm pair)
          (Pipeline.compose (normAlgebra algebra)
            (referenceTransport pair) (backgroundPath pair))
          (Pipeline.compose (normAlgebra algebra)
            (referenceTransport pair) (referencePath pair)))
        (cong
          (Pipeline.compose (normAlgebra algebra) (referenceLogarithm pair))
          (subtractComposedInner algebra
            (referenceTransport pair)
            (backgroundPath pair)
            (referencePath pair)))))

fourStageDifferenceExact :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) →
  subtractOperator algebra
    (backgroundFourStage pair) (referenceFourStage pair)
  ≡ fourDifferenceTermSum pair
fourStageDifferenceExact algebra pair =
  trans
    (fourStageDifferenceTelescope algebra pair)
    (cong
      (λ first → addOperator algebra first
        (addOperator algebra
          (subtractOperator algebra
            (intermediateOne pair) (intermediateTwo pair))
          (addOperator algebra
            (subtractOperator algebra
              (intermediateTwo pair) (intermediateThree pair))
            (subtractOperator algebra
              (intermediateThree pair) (referenceFourStage pair)))))
      (outerDifferenceFactorization algebra pair))
  -- The remaining three rewrites are definitionally nested in the right tail.
  -- Keeping them explicit avoids any commutativity assumption on composition.
  |> λ firstRewrite →
    trans firstRewrite
      (cong
        (addOperator algebra (outerDifferenceTerm pair))
        (trans
          (cong
            (λ second → addOperator algebra second
              (addOperator algebra
                (subtractOperator algebra
                  (intermediateTwo pair) (intermediateThree pair))
                (subtractOperator algebra
                  (intermediateThree pair) (referenceFourStage pair))))
            (logarithmDifferenceFactorization algebra pair))
          (cong
            (addOperator algebra (logarithmDifferenceTerm pair))
            (trans
              (cong
                (λ third → addOperator algebra third
                  (subtractOperator algebra
                    (intermediateThree pair) (referenceFourStage pair)))
                (transportDifferenceFactorization algebra pair))
              (cong
                (addOperator algebra (transportDifferenceTerm pair))
                (pathDifferenceFactorization algebra pair))))))
  where
    infixl 0 _|>_
    _|>_ : ∀ {A B : Set} → A → (A → B) → B
    value |> function = function value

record FourStageDifferenceNormInputs
    (Operator Bound : Set)
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra) : Set₁ where
  field
    backgroundOuterBound backgroundLogarithmBound
      backgroundTransportBound backgroundPathBound : Bound
    referenceOuterBound referenceLogarithmBound
      referenceTransportBound referencePathBound : Bound
    outerDifferenceBound logarithmDifferenceBound
      transportDifferenceBound pathDifferenceBound : Bound

    backgroundOuterEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (backgroundOuter pair)) backgroundOuterBound
    backgroundLogarithmEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (backgroundLogarithm pair)) backgroundLogarithmBound
    backgroundTransportEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (backgroundTransport pair)) backgroundTransportBound
    backgroundPathEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (backgroundPath pair)) backgroundPathBound

    referenceOuterEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (referenceOuter pair)) referenceOuterBound
    referenceLogarithmEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (referenceLogarithm pair)) referenceLogarithmBound
    referenceTransportEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (referenceTransport pair)) referenceTransportBound
    referencePathEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (referencePath pair)) referencePathBound

    outerDifferenceEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (subtractOperator algebra
            (backgroundOuter pair) (referenceOuter pair)))
        outerDifferenceBound
    logarithmDifferenceEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (subtractOperator algebra
            (backgroundLogarithm pair) (referenceLogarithm pair)))
        logarithmDifferenceBound
    transportDifferenceEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (subtractOperator algebra
            (backgroundTransport pair) (referenceTransport pair)))
        transportDifferenceBound
    pathDifferenceEstimate :
      Pipeline.LessEqual (normAlgebra algebra)
        (Pipeline.operatorNorm (normAlgebra algebra)
          (subtractOperator algebra
            (backgroundPath pair) (referencePath pair)))
        pathDifferenceBound

open FourStageDifferenceNormInputs public

outerTermBound logarithmTermBound transportTermBound pathTermBound :
  ∀ {Operator Bound algebra pair} →
  FourStageDifferenceNormInputs Operator Bound algebra pair → Bound
outerTermBound {algebra = algebra} inputs =
  Pipeline.multiply (normAlgebra algebra) (outerDifferenceBound inputs)
    (Pipeline.multiply (normAlgebra algebra)
      (backgroundLogarithmBound inputs)
      (Pipeline.multiply (normAlgebra algebra)
        (backgroundTransportBound inputs)
        (backgroundPathBound inputs)))
logarithmTermBound {algebra = algebra} inputs =
  Pipeline.multiply (normAlgebra algebra) (referenceOuterBound inputs)
    (Pipeline.multiply (normAlgebra algebra)
      (logarithmDifferenceBound inputs)
      (Pipeline.multiply (normAlgebra algebra)
        (backgroundTransportBound inputs)
        (backgroundPathBound inputs)))
transportTermBound {algebra = algebra} inputs =
  Pipeline.multiply (normAlgebra algebra) (referenceOuterBound inputs)
    (Pipeline.multiply (normAlgebra algebra)
      (referenceLogarithmBound inputs)
      (Pipeline.multiply (normAlgebra algebra)
        (transportDifferenceBound inputs)
        (backgroundPathBound inputs)))
pathTermBound {algebra = algebra} inputs =
  Pipeline.multiply (normAlgebra algebra) (referenceOuterBound inputs)
    (Pipeline.multiply (normAlgebra algebra)
      (referenceLogarithmBound inputs)
      (Pipeline.multiply (normAlgebra algebra)
        (referenceTransportBound inputs)
        (pathDifferenceBound inputs)))

fourStageDifferenceMajorant :
  ∀ {Operator Bound algebra pair} →
  FourStageDifferenceNormInputs Operator Bound algebra pair → Bound
fourStageDifferenceMajorant {algebra = algebra} inputs =
  addBound algebra (outerTermBound inputs)
    (addBound algebra (logarithmTermBound inputs)
      (addBound algebra
        (transportTermBound inputs)
        (pathTermBound inputs)))

outerDifferenceTermNormBound :
  ∀ {Operator Bound algebra pair}
    (inputs : FourStageDifferenceNormInputs Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (outerDifferenceTerm pair))
    (outerTermBound inputs)
outerDifferenceTermNormBound {algebra = algebra} {pair = pair} inputs =
  Pipeline.fourStageNormBound (normAlgebra algebra)
    (subtractOperator algebra
      (backgroundOuter pair) (referenceOuter pair))
    (backgroundLogarithm pair)
    (backgroundTransport pair)
    (backgroundPath pair)
    (outerDifferenceBound inputs)
    (backgroundLogarithmBound inputs)
    (backgroundTransportBound inputs)
    (backgroundPathBound inputs)
    (outerDifferenceEstimate inputs)
    (backgroundLogarithmEstimate inputs)
    (backgroundTransportEstimate inputs)
    (backgroundPathEstimate inputs)

logarithmDifferenceTermNormBound :
  ∀ {Operator Bound algebra pair}
    (inputs : FourStageDifferenceNormInputs Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (logarithmDifferenceTerm pair))
    (logarithmTermBound inputs)
logarithmDifferenceTermNormBound {algebra = algebra} {pair = pair} inputs =
  Pipeline.fourStageNormBound (normAlgebra algebra)
    (referenceOuter pair)
    (subtractOperator algebra
      (backgroundLogarithm pair) (referenceLogarithm pair))
    (backgroundTransport pair)
    (backgroundPath pair)
    (referenceOuterBound inputs)
    (logarithmDifferenceBound inputs)
    (backgroundTransportBound inputs)
    (backgroundPathBound inputs)
    (referenceOuterEstimate inputs)
    (logarithmDifferenceEstimate inputs)
    (backgroundTransportEstimate inputs)
    (backgroundPathEstimate inputs)

transportDifferenceTermNormBound :
  ∀ {Operator Bound algebra pair}
    (inputs : FourStageDifferenceNormInputs Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (transportDifferenceTerm pair))
    (transportTermBound inputs)
transportDifferenceTermNormBound {algebra = algebra} {pair = pair} inputs =
  Pipeline.fourStageNormBound (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (subtractOperator algebra
      (backgroundTransport pair) (referenceTransport pair))
    (backgroundPath pair)
    (referenceOuterBound inputs)
    (referenceLogarithmBound inputs)
    (transportDifferenceBound inputs)
    (backgroundPathBound inputs)
    (referenceOuterEstimate inputs)
    (referenceLogarithmEstimate inputs)
    (transportDifferenceEstimate inputs)
    (backgroundPathEstimate inputs)

pathDifferenceTermNormBound :
  ∀ {Operator Bound algebra pair}
    (inputs : FourStageDifferenceNormInputs Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (pathDifferenceTerm pair))
    (pathTermBound inputs)
pathDifferenceTermNormBound {algebra = algebra} {pair = pair} inputs =
  Pipeline.fourStageNormBound (normAlgebra algebra)
    (referenceOuter pair)
    (referenceLogarithm pair)
    (referenceTransport pair)
    (subtractOperator algebra
      (backgroundPath pair) (referencePath pair))
    (referenceOuterBound inputs)
    (referenceLogarithmBound inputs)
    (referenceTransportBound inputs)
    (pathDifferenceBound inputs)
    (referenceOuterEstimate inputs)
    (referenceLogarithmEstimate inputs)
    (referenceTransportEstimate inputs)
    (pathDifferenceEstimate inputs)

fourDifferenceTermSumNormBound :
  ∀ {Operator Bound algebra pair}
    (inputs : FourStageDifferenceNormInputs Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (fourDifferenceTermSum pair))
    (fourStageDifferenceMajorant inputs)
fourDifferenceTermSumNormBound {algebra = algebra} {pair = pair} inputs =
  Pipeline.transitive (normAlgebra algebra)
    (normAddTriangle algebra
      (outerDifferenceTerm pair)
      (addOperator algebra (logarithmDifferenceTerm pair)
        (addOperator algebra
          (transportDifferenceTerm pair)
          (pathDifferenceTerm pair))))
    (addBoundMonotone algebra
      (outerDifferenceTermNormBound inputs)
      (Pipeline.transitive (normAlgebra algebra)
        (normAddTriangle algebra
          (logarithmDifferenceTerm pair)
          (addOperator algebra
            (transportDifferenceTerm pair)
            (pathDifferenceTerm pair)))
        (addBoundMonotone algebra
          (logarithmDifferenceTermNormBound inputs)
          (Pipeline.transitive (normAlgebra algebra)
            (normAddTriangle algebra
              (transportDifferenceTerm pair)
              (pathDifferenceTerm pair))
            (addBoundMonotone algebra
              (transportDifferenceTermNormBound inputs)
              (pathDifferenceTermNormBound inputs))))))

fourStageDifferenceNormBound :
  ∀ {Operator Bound}
    (algebra : AdditiveOperatorNormAlgebra Operator Bound)
    (pair : FourStageBackgroundPair Operator Bound algebra)
    (inputs : FourStageDifferenceNormInputs
      Operator Bound algebra pair) →
  Pipeline.LessEqual (normAlgebra algebra)
    (Pipeline.operatorNorm (normAlgebra algebra)
      (subtractOperator algebra
        (backgroundFourStage pair) (referenceFourStage pair)))
    (fourStageDifferenceMajorant inputs)
fourStageDifferenceNormBound algebra pair inputs =
  subst
    (λ selected → Pipeline.LessEqual (normAlgebra algebra)
      (Pipeline.operatorNorm (normAlgebra algebra) selected)
      (fourStageDifferenceMajorant inputs))
    (sym (fourStageDifferenceExact algebra pair))
    (fourDifferenceTermSumNormBound inputs)

fourStageOperatorDifferenceTelescopeLevel : ProofLevel
fourStageOperatorDifferenceTelescopeLevel = machineChecked

fourStageOperatorDifferenceNormLevel : ProofLevel
fourStageOperatorDifferenceNormLevel = machineChecked

cmp109DerivativeDifferenceFourLeafReductionLevel : ProofLevel
cmp109DerivativeDifferenceFourLeafReductionLevel = machineChecked
