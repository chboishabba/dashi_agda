module DASHI.Physics.YangMills.BalabanClayGate4QuantitativeImplicitFunctionCommonExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Shared quantitative implicit/inverse-function infrastructure.
--
-- J. M. Holtzman,
-- "Explicit epsilon and delta for the Implicit Function Theorem",
-- SIAM Review 12 (2) (1970), 284--286.
-- DOI: 10.1137/1012051.
--
-- Marco Papi,
-- "On the Domain of the Implicit Function and Applications",
-- Journal of Inequalities and Applications 2005 (2005), 221--234.
-- DOI: 10.1155/JIA.2005.221.
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators",
-- Springer Classics in Mathematics (1995 reprint).
-- DOI: 10.1007/978-3-642-66282-9.
--
-- The Federbush group average and the tree/background gauge transition need
-- the same analytic mechanism: an invariant ball, a strict contraction on that
-- ball, and stability of an invertible centre differential under a relatively
-- small perturbation.  The finite algebra below is shared by both consumers.
-- Completeness/fixed-point existence and the physical Lipschitz constants stay
-- explicit; uniqueness, residual uniqueness and triviality of the perturbed
-- kernel are derived rather than repeated as separate assumptions.
------------------------------------------------------------------------

record QuantitativeMetricAlgebra
    (Point Bound : Set) : Set₁ where
  field
    distance : Point → Point → Bound
    zeroBound : Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set

    reflexive : ∀ value → LessEqual value value
    transitive : ∀ {left middle right} →
      LessEqual left middle → LessEqual middle right → LessEqual left right

    distanceSelf : ∀ point → distance point point ≡ zeroBound
    zeroDistanceImpliesEqual : ∀ left right →
      distance left right ≡ zeroBound → left ≡ right

    -- This is the scalar order fact used by every strict-contraction proof:
    -- d <= q d with q < 1 forces d = 0.
    contractionForcesZero : ∀ factor value →
      StrictlyBelowOne factor →
      LessEqual value (multiply factor value) →
      value ≡ zeroBound

open QuantitativeMetricAlgebra public

record InvariantContractionBall
    {Point Bound : Set}
    (metric : QuantitativeMetricAlgebra Point Bound) : Set₁ where
  field
    centre : Point
    radius contractionFactor : Bound
    map : Point → Point

    InBall : Point → Set
    inBallMeaning : ∀ point →
      InBall point ≡ LessEqual metric (distance metric point centre) radius

    mapPreservesBall : ∀ point → InBall point → InBall (map point)

    mapContractive : ∀ left right →
      InBall left → InBall right →
      LessEqual metric
        (distance metric (map left) (map right))
        (multiply metric contractionFactor (distance metric left right))

    contractionFactorBelowOne :
      StrictlyBelowOne metric contractionFactor

open InvariantContractionBall public

record FixedPointWitness
    {Point Bound : Set}
    {metric : QuantitativeMetricAlgebra Point Bound}
    (ball : InvariantContractionBall metric) : Set where
  field
    point : Point
    pointInBall : InBall ball point
    pointFixed : map ball point ≡ point

open FixedPointWitness public

fixedPointDistanceContractsItself :
  ∀ {Point Bound}
    {metric : QuantitativeMetricAlgebra Point Bound}
    (ball : InvariantContractionBall metric)
    left right →
  InBall ball left → InBall ball right →
  map ball left ≡ left → map ball right ≡ right →
  LessEqual metric
    (distance metric left right)
    (multiply metric (contractionFactor ball)
      (distance metric left right))
fixedPointDistanceContractsItself {metric = metric} ball left right
    leftIn rightIn leftFixed rightFixed =
  subst
    (λ distanceAfter →
      LessEqual metric distanceAfter
        (multiply metric (contractionFactor ball)
          (distance metric left right)))
    (cong₂ (distance metric) leftFixed rightFixed)
    (mapContractive ball left right leftIn rightIn)

fixedPointUniqueInInvariantBall :
  ∀ {Point Bound}
    {metric : QuantitativeMetricAlgebra Point Bound}
    (ball : InvariantContractionBall metric)
    left right →
  InBall ball left → InBall ball right →
  map ball left ≡ left → map ball right ≡ right →
  left ≡ right
fixedPointUniqueInInvariantBall {metric = metric} ball left right
    leftIn rightIn leftFixed rightFixed =
  zeroDistanceImpliesEqual metric left right
    (contractionForcesZero metric
      (contractionFactor ball)
      (distance metric left right)
      (contractionFactorBelowOne ball)
      (fixedPointDistanceContractsItself
        ball left right leftIn rightIn leftFixed rightFixed))

record QuantitativeImplicitFunctionData
    (Input Output Bound : Set) : Set₁ where
  field
    metric : QuantitativeMetricAlgebra Output Bound
    AdmissibleInput : Input → Set
    contractionBall : Input → InvariantContractionBall metric

    ResidualZero : Input → Output → Set

    fixedPointImpliesResidualZero : ∀ input output →
      InBall (contractionBall input) output →
      map (contractionBall input) output ≡ output →
      ResidualZero input output

    residualZeroImpliesFixedPoint : ∀ input output →
      InBall (contractionBall input) output →
      ResidualZero input output →
      map (contractionBall input) output ≡ output

    -- Supplied by the quantitative Banach fixed-point theorem after the
    -- repository proves completeness, ball invariance and the scalar radius
    -- inequalities for the selected finite-dimensional norm.
    fixedPointExists : ∀ input → AdmissibleInput input →
      FixedPointWitness (contractionBall input)

open QuantitativeImplicitFunctionData public

implicitSolution :
  ∀ {Input Output Bound}
    (dataSet : QuantitativeImplicitFunctionData Input Output Bound)
    input → AdmissibleInput dataSet input → Output
implicitSolution dataSet input admissible =
  point (fixedPointExists dataSet input admissible)

implicitSolutionInBall :
  ∀ {Input Output Bound}
    (dataSet : QuantitativeImplicitFunctionData Input Output Bound)
    input (admissible : AdmissibleInput dataSet input) →
  InBall (contractionBall dataSet input)
    (implicitSolution dataSet input admissible)
implicitSolutionInBall dataSet input admissible =
  pointInBall (fixedPointExists dataSet input admissible)

implicitSolutionSolvesResidual :
  ∀ {Input Output Bound}
    (dataSet : QuantitativeImplicitFunctionData Input Output Bound)
    input (admissible : AdmissibleInput dataSet input) →
  ResidualZero dataSet input
    (implicitSolution dataSet input admissible)
implicitSolutionSolvesResidual dataSet input admissible =
  fixedPointImpliesResidualZero dataSet input
    (implicitSolution dataSet input admissible)
    (implicitSolutionInBall dataSet input admissible)
    (pointFixed (fixedPointExists dataSet input admissible))

residualSolutionUniqueInQuantitativeBall :
  ∀ {Input Output Bound}
    (dataSet : QuantitativeImplicitFunctionData Input Output Bound)
    input (admissible : AdmissibleInput dataSet input)
    candidate →
  InBall (contractionBall dataSet input) candidate →
  ResidualZero dataSet input candidate →
  candidate ≡ implicitSolution dataSet input admissible
residualSolutionUniqueInQuantitativeBall dataSet input admissible candidate
    candidateIn candidateResidual =
  fixedPointUniqueInInvariantBall
    (contractionBall dataSet input)
    candidate
    (implicitSolution dataSet input admissible)
    candidateIn
    (implicitSolutionInBall dataSet input admissible)
    (residualZeroImpliesFixedPoint dataSet input candidate
      candidateIn candidateResidual)
    (pointFixed (fixedPointExists dataSet input admissible))

------------------------------------------------------------------------
-- Explicit scalar radius ledger.
------------------------------------------------------------------------

record QuantitativeRadiusBudget (Bound : Set) : Set₁ where
  field
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set
    StrictlyBelowOne : Bound → Set

    inverseNormBound derivativeLipschitzBound : Bound
    inputRadius outputRadius forcingBound contractionFactor : Bound

    contractionFactorMeaning :
      contractionFactor
      ≡ multiply inverseNormBound
          (multiply derivativeLipschitzBound outputRadius)

    contractionFactorBelowOne : StrictlyBelowOne contractionFactor

    forcingFitsOutputBall :
      LessEqual
        (multiply inverseNormBound forcingBound)
        outputRadius

    inputRadiusControlsForcing : Set

open QuantitativeRadiusBudget public

------------------------------------------------------------------------
-- Relative inverse stability: the common centre-differential theorem.
------------------------------------------------------------------------

record RelativeInverseKernelData
    (Vector Bound : Set) : Set₁ where
  field
    metric : QuantitativeMetricAlgebra Vector Bound
    zeroVector : Vector
    norm : Vector → Bound

    operator defectMap : Vector → Vector
    Kernel : Vector → Set

    relativeFactor : Bound
    relativeFactorBelowOne :
      StrictlyBelowOne metric relativeFactor

    kernelImpliesDefectFixedPoint : ∀ vector →
      Kernel vector → vector ≡ defectMap vector

    defectNormBound : ∀ vector →
      LessEqual metric
        (norm (defectMap vector))
        (multiply metric relativeFactor (norm vector))

    normZeroImpliesVectorZero : ∀ vector →
      norm vector ≡ zeroBound metric → vector ≡ zeroVector

open RelativeInverseKernelData public

substLower :
  ∀ {A : Set} {Relation : A → A → Set}
    {left right upper : A} →
  left ≡ right → Relation right upper → Relation left upper
substLower refl proof = proof

relativeInverseKernelTrivial :
  ∀ {Vector Bound}
    (dataSet : RelativeInverseKernelData Vector Bound)
    vector → Kernel dataSet vector →
  vector ≡ zeroVector dataSet
relativeInverseKernelTrivial dataSet vector kernel =
  normZeroImpliesVectorZero dataSet vector
    (contractionForcesZero (metric dataSet)
      (relativeFactor dataSet)
      (norm dataSet vector)
      (relativeFactorBelowOne dataSet)
      (subst
        (λ normed →
          LessEqual (metric dataSet) normed
            (multiply (metric dataSet) (relativeFactor dataSet)
              (norm dataSet vector)))
        (sym (cong (norm dataSet)
          (kernelImpliesDefectFixedPoint dataSet vector kernel)))
        (defectNormBound dataSet vector)))

record FiniteSquareInverseUpgrade
    (Vector : Set)
    (operator : Vector → Vector) : Set₁ where
  field
    inverse : Vector → Vector
    zeroVector : Vector
    Kernel : Vector → Set

    kernelMeaning : ∀ vector →
      Kernel vector ≡ (operator vector ≡ zeroVector)

    inverseFromTrivialKernel :
      (∀ vector → Kernel vector → vector ≡ zeroVector) →
      (∀ vector → inverse (operator vector) ≡ vector)

    operatorAfterInverseFromTrivialKernel :
      (∀ vector → Kernel vector → vector ≡ zeroVector) →
      (∀ vector → operator (inverse vector) ≡ vector)

open FiniteSquareInverseUpgrade public

quantitativeContractionUniquenessLevel : ProofLevel
quantitativeContractionUniquenessLevel = machineChecked

quantitativeResidualSolutionUniquenessLevel : ProofLevel
quantitativeResidualSolutionUniquenessLevel = machineChecked

relativeInverseKernelTrivialityLevel : ProofLevel
relativeInverseKernelTrivialityLevel = machineChecked

quantitativeBanachFixedPointExistenceLevel : ProofLevel
quantitativeBanachFixedPointExistenceLevel = standardImported

finiteSquareTrivialKernelInverseUpgradeLevel : ProofLevel
finiteSquareTrivialKernelInverseUpgradeLevel = standardImported

physicalQuantitativeRadiusConstantsInputsLevel : ProofLevel
physicalQuantitativeRadiusConstantsInputsLevel = conditional

physicalCompletenessAndBallInvarianceInputsLevel : ProofLevel
physicalCompletenessAndBallInvarianceInputsLevel = conditional
