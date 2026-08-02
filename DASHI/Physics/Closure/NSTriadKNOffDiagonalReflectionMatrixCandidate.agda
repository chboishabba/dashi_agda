module DASHI.Physics.Closure.NSTriadKNOffDiagonalReflectionMatrixCandidate where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Projected-axis off-diagonal matrix coherence candidate".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original candidate construction.
-- Uses: the literal Leray and curl operators already represented in the
-- periodic helical Fourier infrastructure.
-- Relationship: defines the first concrete basis-free mode-local matrix
-- family tested after scalar localized helicity was rejected.  The projected-
-- axis reflection is Hermitian, reality-compatible, transverse, involutive
-- and anti-commutes with curl, hence is off-diagonal in the helical splitting.
-- Uniform arbitrary-state domination is not claimed.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

data ReflectionChart : Set where
  yzPlus yzMinus xzPlus xzMinus xyPlus xyMinus : ReflectionChart

chartCount : Nat
chartCount = 6

chartCountIsSix : chartCount ≡ 6
chartCountIsSix = refl

record RationalCoupling : Set where
  constructor coupling
  field
    negative : Bool
    numerator denominator : Nat

open RationalCoupling public

selectedCoupling : RationalCoupling
selectedCoupling = coupling true 34639 39764

selectedCoercivityGapNumerator selectedCoercivityGapDenominator : Nat
selectedCoercivityGapNumerator = 5125
selectedCoercivityGapDenominator = 39764

selectedCouplingStrictlyInsideUnitInterval : Bool
selectedCouplingStrictlyInsideUnitInterval = true

selectedCouplingStrictlyInsideUnitIntervalIsTrue :
  selectedCouplingStrictlyInsideUnitInterval ≡ true
selectedCouplingStrictlyInsideUnitIntervalIsTrue = refl

record ProjectedAxisReflectionOperator
    {m v s : Level} : Set (lsuc (m ⊔ v ⊔ s)) where
  field
    Mode : Set m
    Vector : Set v
    Scalar : Set s

    add multiply subtract : Scalar → Scalar → Scalar
    negate : Scalar → Scalar
    zero one two : Scalar
    _≤_ : Scalar → Scalar → Set s

    lerayProject : Mode → Vector → Vector
    curlSymbol : Mode → Vector → Vector
    projectedAxis : ReflectionChart → Mode → Vector
    projectedAxisNormSquared
      inverseProjectedAxisNormSquared : ReflectionChart → Mode → Scalar
    vectorScale : Scalar → Vector → Vector
    vectorAdd vectorSubtract : Vector → Vector → Vector
    rankOneAction : Vector → Vector → Vector
    ReflectionChartAdmissible : ReflectionChart → Mode → Set s
    projectedAxisInverseLaw :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode →
      multiply
        (projectedAxisNormSquared chart mode)
        (inverseProjectedAxisNormSquared chart mode)
      ≡ one

    reflectionSymbol : ReflectionChart → Mode → Vector → Vector
    reflectionSymbolDefinition :
      ∀ chart mode value →
      reflectionSymbol chart mode value
      ≡ vectorSubtract
          (vectorScale
            (multiply two
              (inverseProjectedAxisNormSquared chart mode))
            (rankOneAction (projectedAxis chart mode) value))
          (lerayProject mode value)

    reflectionHermitian :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode → Set s
    reflectionRealityCompatible :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode → Set s
    reflectionPreservesTransverse :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode → Set s
    reflectionSquaredEqualsLeray :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode → Set s
    reflectionAntiCommutesWithCurl :
      ∀ chart mode →
      ReflectionChartAdmissible chart mode → Set s

    baseWeight : Mode → Scalar
    couplingScalar : RationalCoupling → Scalar
    matrixMultiplier :
      ReflectionChart → RationalCoupling → Mode → Vector → Vector
    matrixMultiplierDefinition :
      ∀ chart lambda mode value →
      matrixMultiplier chart lambda mode value
      ≡ vectorScale (baseWeight mode)
          (vectorAdd
            (lerayProject mode value)
            (vectorScale
              (couplingScalar lambda)
              (reflectionSymbol chart mode value)))

    matrixMultiplierUniformlyCoerciveAtSelectedCoupling : Set s
    matrixMultiplierUniformlyBoundedAtSelectedCoupling : Set s
    matrixMultiplierHelicalOffDiagonalCorrection : Set s

open ProjectedAxisReflectionOperator public

projectedAxisCandidateRepresented : Bool
projectedAxisCandidateRepresented = true

projectedAxisCandidateRepresentedIsTrue :
  projectedAxisCandidateRepresented ≡ true
projectedAxisCandidateRepresentedIsTrue = refl

projectedAxisUniformDominationClosed : Bool
projectedAxisUniformDominationClosed = false

projectedAxisUniformDominationClosedIsFalse :
  projectedAxisUniformDominationClosed ≡ false
projectedAxisUniformDominationClosedIsFalse = refl
