module DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact where

------------------------------------------------------------------------
-- REFINEMENT-INDEXED ONE-STEP ERRORS -> COMPLETE CMP119 (2.18) ERROR
--
-- For each refinement n:
--
--   one-step errors
--      -> ordered component product       (2.20)/(2.22)
--      -> product over components         (2.19)
--      -> sum over admissible sequences   (2.18).
--
-- The source factors and ordinary majorants are refinement-independent.
-- Approximate factors and their marked errors are refinement-indexed.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_; _-ℝ_; absℝ; _≤ℝ_;
   ≤ℝ-refl; ≤ℝ-trans; +-mono-≤; +-identityˡ;
   absMul; mulMonotoneNonnegative; mulSubDistributes)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
import DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact as Product
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as Sums
import DASHI.Physics.YangMills.BalabanCompactHaarFiniteQuadratureErrorExact as SumError

record CMP119FactorizedDensityApproximation
    (SlowField Sequence Component Step : Set) : Set₁ where
  field
    admissibleSequences : Nat → List Sequence
    componentsAt : Nat → Sequence → List Component
    orderedStepsAt : Nat → Sequence → Component → List Step

    sourceStep :
      Nat → Sequence → Component → Step → SlowField → ℝ

    approximateStep :
      Nat → Nat → Sequence → Component → Step → SlowField → ℝ

    ordinaryMajorant :
      Nat → Sequence → Component → Step → SlowField → ℝ

    markedMajorant :
      Nat → Nat → Sequence → Component → Step → SlowField → ℝ

    residualFactor residualMajorant :
      Nat → Sequence → SlowField → ℝ

    ordinaryNonnegative :
      ∀ scale sequence component step slow →
      0ℝ ≤ℝ ordinaryMajorant
        scale sequence component step slow

    markedNonnegative :
      ∀ refinement scale sequence component step slow →
      0ℝ ≤ℝ markedMajorant
        refinement scale sequence component step slow

    sourceStepBound :
      ∀ scale sequence component step slow →
      absℝ (sourceStep
        scale sequence component step slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    approximateStepBound :
      ∀ refinement scale sequence component step slow →
      absℝ (approximateStep
        refinement scale sequence component step slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    stepDifferenceBound :
      ∀ refinement scale sequence component step slow →
      absℝ
        (sourceStep scale sequence component step slow
          -ℝ
         approximateStep refinement scale sequence component step slow)
      ≤ℝ markedMajorant
        refinement scale sequence component step slow

    residualMajorantNonnegative :
      ∀ scale sequence slow →
      0ℝ ≤ℝ residualMajorant scale sequence slow

    residualBound :
      ∀ scale sequence slow →
      absℝ (residualFactor scale sequence slow)
      ≤ℝ residualMajorant scale sequence slow

open CMP119FactorizedDensityApproximation public

componentSource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentSource dataSet scale sequence component slow =
  Hess.productℝ
    (λ step → sourceStep dataSet scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → Component → SlowField → ℝ
componentApproximation dataSet refinement scale sequence component slow =
  Hess.productℝ
    (λ step → approximateStep dataSet
      refinement scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentOrdinaryMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentOrdinaryMajorant dataSet scale sequence component slow =
  Hess.productℝ
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentMarkedMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → Component → SlowField → ℝ
componentMarkedMajorant dataSet refinement scale sequence component slow =
  Product.markedProductMajorant
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (λ step → markedMajorant dataSet
      refinement scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

zeroSumNonnegative :
  ∀ {left right : ℝ} →
  0ℝ ≤ℝ left →
  0ℝ ≤ℝ right →
  0ℝ ≤ℝ left +ℝ right
zeroSumNonnegative leftNN rightNN =
  Hess.replaceLeft≤
    (+-identityˡ 0ℝ)
    (+-mono-≤ leftNN rightNN)

markedProductMajorantNonnegative :
  ∀ {A : Set}
    (ordinary marked : A → ℝ)
    (xs : List A) →
  (∀ x → 0ℝ ≤ℝ ordinary x) →
  (∀ x → 0ℝ ≤ℝ marked x) →
  0ℝ ≤ℝ Product.markedProductMajorant ordinary marked xs
markedProductMajorantNonnegative ordinary marked [] ordinaryNN markedNN =
  ≤ℝ-refl
markedProductMajorantNonnegative ordinary marked (x ∷ xs)
  ordinaryNN markedNN =
  zeroSumNonnegative
    (Hess.zeroProduct≤
      (marked x)
      (Hess.productℝ ordinary xs)
      (markedNN x)
      (Hess.productNonnegative ordinary xs ordinaryNN))
    (Hess.zeroProduct≤
      (ordinary x)
      (Product.markedProductMajorant ordinary marked xs)
      (ordinaryNN x)
      (markedProductMajorantNonnegative
        ordinary marked xs ordinaryNN markedNN))

componentOrdinaryNonnegative :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    scale sequence component slow →
  0ℝ ≤ℝ componentOrdinaryMajorant dataSet scale sequence component slow
componentOrdinaryNonnegative dataSet scale sequence component slow =
  Hess.productNonnegative
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet scale sequence component step slow)

componentMarkedNonnegative :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale sequence component slow →
  0ℝ ≤ℝ componentMarkedMajorant
    dataSet refinement scale sequence component slow
componentMarkedNonnegative dataSet refinement scale sequence component slow =
  markedProductMajorantNonnegative
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (λ step → markedMajorant dataSet
      refinement scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet scale sequence component step slow)
    (λ step → markedNonnegative dataSet
      refinement scale sequence component step slow)

componentSourceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    scale sequence component slow →
  absℝ (componentSource dataSet scale sequence component slow)
  ≤ℝ componentOrdinaryMajorant dataSet scale sequence component slow
componentSourceBound dataSet scale sequence component slow =
  Product.absProductBelowProductMajorant
    (λ step → sourceStep dataSet scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet scale sequence component step slow)
    (λ step → sourceStepBound dataSet scale sequence component step slow)

componentApproximationBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale sequence component slow →
  absℝ (componentApproximation
    dataSet refinement scale sequence component slow)
  ≤ℝ componentOrdinaryMajorant dataSet scale sequence component slow
componentApproximationBound dataSet refinement scale sequence component slow =
  Product.absProductBelowProductMajorant
    (λ step → approximateStep dataSet
      refinement scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet scale sequence component step slow)
    (λ step → approximateStepBound dataSet
      refinement scale sequence component step slow)

componentDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale sequence component slow →
  absℝ
    (componentSource dataSet scale sequence component slow
      -ℝ
     componentApproximation
       dataSet refinement scale sequence component slow)
  ≤ℝ componentMarkedMajorant
    dataSet refinement scale sequence component slow
componentDifferenceBound dataSet refinement scale sequence component slow =
  Product.markedProductDifferenceFromFactorwiseBounds
    (λ step → sourceStep dataSet scale sequence component step slow)
    (λ step → approximateStep dataSet
      refinement scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet scale sequence component step slow)
    (λ step → markedMajorant dataSet
      refinement scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet scale sequence component step slow)
    (λ step → sourceStepBound dataSet scale sequence component step slow)
    (λ step → approximateStepBound dataSet
      refinement scale sequence component step slow)
    (λ step → stepDifferenceBound dataSet
      refinement scale sequence component step slow)

componentProductSource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
componentProductSource dataSet scale sequence slow =
  Hess.productℝ
    (λ component → componentSource dataSet scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → SlowField → ℝ
componentProductApproximation dataSet refinement scale sequence slow =
  Hess.productℝ
    (λ component → componentApproximation
      dataSet refinement scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductMarkedMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → SlowField → ℝ
componentProductMarkedMajorant dataSet refinement scale sequence slow =
  Product.markedProductMajorant
    (λ component → componentOrdinaryMajorant
      dataSet scale sequence component slow)
    (λ component → componentMarkedMajorant
      dataSet refinement scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale sequence slow →
  absℝ
    (componentProductSource dataSet scale sequence slow
      -ℝ
     componentProductApproximation
       dataSet refinement scale sequence slow)
  ≤ℝ componentProductMarkedMajorant
    dataSet refinement scale sequence slow
componentProductDifferenceBound dataSet refinement scale sequence slow =
  Product.markedProductDifferenceFromFactorwiseBounds
    (λ component → componentSource dataSet scale sequence component slow)
    (λ component → componentApproximation
      dataSet refinement scale sequence component slow)
    (λ component → componentOrdinaryMajorant
      dataSet scale sequence component slow)
    (λ component → componentMarkedMajorant
      dataSet refinement scale sequence component slow)
    (componentsAt dataSet scale sequence)
    (λ component → componentOrdinaryNonnegative
      dataSet scale sequence component slow)
    (λ component → componentSourceBound
      dataSet scale sequence component slow)
    (λ component → componentApproximationBound
      dataSet refinement scale sequence component slow)
    (λ component → componentDifferenceBound
      dataSet refinement scale sequence component slow)

sequenceSource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
sequenceSource dataSet scale sequence slow =
  residualFactor dataSet scale sequence slow
  *ℝ componentProductSource dataSet scale sequence slow

sequenceApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → SlowField → ℝ
sequenceApproximation dataSet refinement scale sequence slow =
  residualFactor dataSet scale sequence slow
  *ℝ componentProductApproximation
    dataSet refinement scale sequence slow

sequenceErrorBudget :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → Sequence → SlowField → ℝ
sequenceErrorBudget dataSet refinement scale sequence slow =
  residualMajorant dataSet scale sequence slow
  *ℝ componentProductMarkedMajorant
    dataSet refinement scale sequence slow

sequenceDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale sequence slow →
  absℝ
    (sequenceSource dataSet scale sequence slow
      -ℝ
     sequenceApproximation
       dataSet refinement scale sequence slow)
  ≤ℝ sequenceErrorBudget dataSet refinement scale sequence slow
sequenceDifferenceBound dataSet refinement scale sequence slow =
  let
    residual = residualFactor dataSet scale sequence slow
    sourceProduct = componentProductSource dataSet scale sequence slow
    approxProduct = componentProductApproximation
      dataSet refinement scale sequence slow

    factored :
      residual *ℝ (sourceProduct -ℝ approxProduct)
      ≡
      sequenceSource dataSet scale sequence slow
        -ℝ
      sequenceApproximation dataSet refinement scale sequence slow
    factored = mulSubDistributes residual sourceProduct approxProduct

    scaled :
      absℝ (residual *ℝ (sourceProduct -ℝ approxProduct))
      ≤ℝ
      sequenceErrorBudget dataSet refinement scale sequence slow
    scaled
      rewrite absMul residual (sourceProduct -ℝ approxProduct) =
      mulMonotoneNonnegative
        (Product.absNonnegative residual)
        (residualBound dataSet scale sequence slow)
        (Product.absNonnegative (sourceProduct -ℝ approxProduct))
        (componentProductDifferenceBound
          dataSet refinement scale sequence slow)
  in
  subst
    (λ difference →
      absℝ difference
      ≤ℝ sequenceErrorBudget dataSet refinement scale sequence slow)
    factored
    scaled

densitySource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → SlowField → ℝ
densitySource dataSet scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence → sequenceSource dataSet scale sequence slow)

densityApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → SlowField → ℝ
densityApproximation dataSet refinement scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceApproximation dataSet refinement scale sequence slow)

densityErrorBudget :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation SlowField Sequence Component Step →
  Nat → Nat → SlowField → ℝ
densityErrorBudget dataSet refinement scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceErrorBudget dataSet refinement scale sequence slow)

factorizedDensityDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet : CMP119FactorizedDensityApproximation
      SlowField Sequence Component Step)
    refinement scale slow →
  absℝ
    (densitySource dataSet scale slow
      -ℝ
     densityApproximation dataSet refinement scale slow)
  ≤ℝ densityErrorBudget dataSet refinement scale slow
factorizedDensityDifferenceBound dataSet refinement scale slow =
  ≤ℝ-trans
    (SumError.absDifferenceOfRealSumsBelowPointwiseAbs
      (admissibleSequences dataSet scale)
      (λ sequence → sequenceSource dataSet scale sequence slow)
      (λ sequence →
        sequenceApproximation dataSet refinement scale sequence slow))
    (SumError.realSumMonotone
      (admissibleSequences dataSet scale)
      (λ sequence →
        absℝ
          (sequenceSource dataSet scale sequence slow
            -ℝ
           sequenceApproximation dataSet refinement scale sequence slow))
      (λ sequence →
        sequenceErrorBudget dataSet refinement scale sequence slow)
      (λ sequence →
        sequenceDifferenceBound dataSet refinement scale sequence slow))

cmp119OneStepToComponentErrorCompilerLevel : ProofLevel
cmp119OneStepToComponentErrorCompilerLevel = machineChecked

cmp119ComponentToSequenceErrorCompilerLevel : ProofLevel
cmp119ComponentToSequenceErrorCompilerLevel = machineChecked

cmp119SequenceToDensityErrorCompilerLevel : ProofLevel
cmp119SequenceToDensityErrorCompilerLevel = machineChecked
