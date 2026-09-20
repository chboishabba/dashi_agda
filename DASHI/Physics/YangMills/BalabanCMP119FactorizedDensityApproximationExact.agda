module DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact where

------------------------------------------------------------------------
-- FACTORWISE ONE-STEP ERRORS -> COMPLETE CMP119 (2.18) DENSITY ERROR
--
-- Algebraic propagation through the source factorization:
--
--   one-step errors
--      -> ordered component product       (2.20)/(2.22)
--      -> product over components         (2.19)
--      -> sum over admissible sequences   (2.18).
--
-- No Yang--Mills analytic estimate is assumed beyond factorwise ordinary and
-- marked majorants plus a bound on the exact residual sequence factor.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym)

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

    sourceStep approximateStep :
      Nat → Sequence → Component → Step → SlowField → ℝ

    ordinaryMajorant markedMajorant :
      Nat → Sequence → Component → Step → SlowField → ℝ

    residualFactor residualMajorant :
      Nat → Sequence → SlowField → ℝ

    ordinaryNonnegative :
      ∀ scale sequence component step slow →
      0ℝ ≤ℝ ordinaryMajorant
        scale sequence component step slow

    markedNonnegative :
      ∀ scale sequence component step slow →
      0ℝ ≤ℝ markedMajorant
        scale sequence component step slow

    sourceStepBound :
      ∀ scale sequence component step slow →
      absℝ (sourceStep
        scale sequence component step slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    approximateStepBound :
      ∀ scale sequence component step slow →
      absℝ (approximateStep
        scale sequence component step slow)
      ≤ℝ ordinaryMajorant
        scale sequence component step slow

    stepDifferenceBound :
      ∀ scale sequence component step slow →
      absℝ
        (sourceStep scale sequence component step slow
          -ℝ
         approximateStep scale sequence component step slow)
      ≤ℝ markedMajorant
        scale sequence component step slow

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
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentSource dataSet scale sequence component slow =
  Hess.productℝ
    (λ step → sourceStep dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentApproximation dataSet scale sequence component slow =
  Hess.productℝ
    (λ step → approximateStep dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentOrdinaryMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentOrdinaryMajorant dataSet scale sequence component slow =
  Hess.productℝ
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)

componentMarkedMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → Component → SlowField → ℝ
componentMarkedMajorant dataSet scale sequence component slow =
  Product.markedProductMajorant
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (λ step → markedMajorant dataSet
      scale sequence component step slow)
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
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence component slow →
  0ℝ ≤ℝ componentOrdinaryMajorant
    dataSet scale sequence component slow
componentOrdinaryNonnegative dataSet scale sequence component slow =
  Hess.productNonnegative
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet
      scale sequence component step slow)

componentMarkedNonnegative :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence component slow →
  0ℝ ≤ℝ componentMarkedMajorant
    dataSet scale sequence component slow
componentMarkedNonnegative dataSet scale sequence component slow =
  markedProductMajorantNonnegative
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (λ step → markedMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet
      scale sequence component step slow)
    (λ step → markedNonnegative dataSet
      scale sequence component step slow)

componentSourceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence component slow →
  absℝ (componentSource dataSet scale sequence component slow)
  ≤ℝ componentOrdinaryMajorant dataSet scale sequence component slow
componentSourceBound dataSet scale sequence component slow =
  Product.absProductBelowProductMajorant
    (λ step → sourceStep dataSet
      scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet
      scale sequence component step slow)
    (λ step → sourceStepBound dataSet
      scale sequence component step slow)

componentApproximationBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence component slow →
  absℝ (componentApproximation dataSet scale sequence component slow)
  ≤ℝ componentOrdinaryMajorant dataSet scale sequence component slow
componentApproximationBound dataSet scale sequence component slow =
  Product.absProductBelowProductMajorant
    (λ step → approximateStep dataSet
      scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet
      scale sequence component step slow)
    (λ step → approximateStepBound dataSet
      scale sequence component step slow)

componentDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence component slow →
  absℝ
    (componentSource dataSet scale sequence component slow
      -ℝ
     componentApproximation dataSet scale sequence component slow)
  ≤ℝ componentMarkedMajorant dataSet scale sequence component slow
componentDifferenceBound dataSet scale sequence component slow =
  Product.markedProductDifferenceFromFactorwiseBounds
    (λ step → sourceStep dataSet
      scale sequence component step slow)
    (λ step → approximateStep dataSet
      scale sequence component step slow)
    (λ step → ordinaryMajorant dataSet
      scale sequence component step slow)
    (λ step → markedMajorant dataSet
      scale sequence component step slow)
    (orderedStepsAt dataSet scale sequence component)
    (λ step → ordinaryNonnegative dataSet
      scale sequence component step slow)
    (λ step → sourceStepBound dataSet
      scale sequence component step slow)
    (λ step → approximateStepBound dataSet
      scale sequence component step slow)
    (λ step → stepDifferenceBound dataSet
      scale sequence component step slow)

componentProductSource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
componentProductSource dataSet scale sequence slow =
  Hess.productℝ
    (λ component →
      componentSource dataSet scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
componentProductApproximation dataSet scale sequence slow =
  Hess.productℝ
    (λ component →
      componentApproximation dataSet scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductMarkedMajorant :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
componentProductMarkedMajorant dataSet scale sequence slow =
  Product.markedProductMajorant
    (λ component →
      componentOrdinaryMajorant dataSet scale sequence component slow)
    (λ component →
      componentMarkedMajorant dataSet scale sequence component slow)
    (componentsAt dataSet scale sequence)

componentProductDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence slow →
  absℝ
    (componentProductSource dataSet scale sequence slow
      -ℝ
     componentProductApproximation dataSet scale sequence slow)
  ≤ℝ componentProductMarkedMajorant dataSet scale sequence slow
componentProductDifferenceBound dataSet scale sequence slow =
  Product.markedProductDifferenceFromFactorwiseBounds
    (λ component →
      componentSource dataSet scale sequence component slow)
    (λ component →
      componentApproximation dataSet scale sequence component slow)
    (λ component →
      componentOrdinaryMajorant dataSet scale sequence component slow)
    (λ component →
      componentMarkedMajorant dataSet scale sequence component slow)
    (componentsAt dataSet scale sequence)
    (λ component →
      componentOrdinaryNonnegative dataSet
        scale sequence component slow)
    (λ component →
      componentSourceBound dataSet
        scale sequence component slow)
    (λ component →
      componentApproximationBound dataSet
        scale sequence component slow)
    (λ component →
      componentDifferenceBound dataSet
        scale sequence component slow)

sequenceSource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
sequenceSource dataSet scale sequence slow =
  residualFactor dataSet scale sequence slow
  *ℝ componentProductSource dataSet scale sequence slow

sequenceApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
sequenceApproximation dataSet scale sequence slow =
  residualFactor dataSet scale sequence slow
  *ℝ componentProductApproximation dataSet scale sequence slow

sequenceErrorBudget :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → Sequence → SlowField → ℝ
sequenceErrorBudget dataSet scale sequence slow =
  residualMajorant dataSet scale sequence slow
  *ℝ componentProductMarkedMajorant dataSet scale sequence slow

sequenceDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale sequence slow →
  absℝ
    (sequenceSource dataSet scale sequence slow
      -ℝ
     sequenceApproximation dataSet scale sequence slow)
  ≤ℝ sequenceErrorBudget dataSet scale sequence slow
sequenceDifferenceBound dataSet scale sequence slow =
  let
    residual = residualFactor dataSet scale sequence slow
    sourceProduct = componentProductSource dataSet scale sequence slow
    approxProduct = componentProductApproximation dataSet scale sequence slow

    factored :
      residual *ℝ (sourceProduct -ℝ approxProduct)
      ≡
      sequenceSource dataSet scale sequence slow
        -ℝ
      sequenceApproximation dataSet scale sequence slow
    factored = mulSubDistributes residual sourceProduct approxProduct

    scaled :
      absℝ (residual *ℝ (sourceProduct -ℝ approxProduct))
      ≤ℝ
      sequenceErrorBudget dataSet scale sequence slow
    scaled
      rewrite absMul residual (sourceProduct -ℝ approxProduct) =
      mulMonotoneNonnegative
        (Product.absNonnegative residual)
        (residualBound dataSet scale sequence slow)
        (Product.absNonnegative (sourceProduct -ℝ approxProduct))
        (componentProductDifferenceBound
          dataSet scale sequence slow)
  in
  subst
    (λ difference →
      absℝ difference
      ≤ℝ sequenceErrorBudget dataSet scale sequence slow)
    factored
    scaled

densitySource :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → SlowField → ℝ
densitySource dataSet scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceSource dataSet scale sequence slow)

densityApproximation :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → SlowField → ℝ
densityApproximation dataSet scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceApproximation dataSet scale sequence slow)

densityErrorBudget :
  ∀ {SlowField Sequence Component Step} →
  CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step →
  Nat → SlowField → ℝ
densityErrorBudget dataSet scale slow =
  Sums.realSum
    (admissibleSequences dataSet scale)
    (λ sequence →
      sequenceErrorBudget dataSet scale sequence slow)

factorizedDensityDifferenceBound :
  ∀ {SlowField Sequence Component Step}
    (dataSet :
      CMP119FactorizedDensityApproximation
        SlowField Sequence Component Step)
    scale slow →
  absℝ
    (densitySource dataSet scale slow
      -ℝ
     densityApproximation dataSet scale slow)
  ≤ℝ densityErrorBudget dataSet scale slow
factorizedDensityDifferenceBound dataSet scale slow =
  ≤ℝ-trans
    (SumError.absDifferenceOfRealSumsBelowPointwiseAbs
      (admissibleSequences dataSet scale)
      (λ sequence →
        sequenceSource dataSet scale sequence slow)
      (λ sequence →
        sequenceApproximation dataSet scale sequence slow))
    (SumError.realSumMonotone
      (admissibleSequences dataSet scale)
      (λ sequence →
        absℝ
          (sequenceSource dataSet scale sequence slow
            -ℝ
           sequenceApproximation dataSet scale sequence slow))
      (λ sequence →
        sequenceErrorBudget dataSet scale sequence slow)
      (λ sequence →
        sequenceDifferenceBound dataSet scale sequence slow))

cmp119OneStepToComponentErrorCompilerLevel : ProofLevel
cmp119OneStepToComponentErrorCompilerLevel = machineChecked

cmp119ComponentToSequenceErrorCompilerLevel : ProofLevel
cmp119ComponentToSequenceErrorCompilerLevel = machineChecked

cmp119SequenceToDensityErrorCompilerLevel : ProofLevel
cmp119SequenceToDensityErrorCompilerLevel = machineChecked
