module DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact where

------------------------------------------------------------------------
-- SHARP FINITE DEGREE-ONE GEOMETRIC BOUND
--
-- From the finite identity
--
--   (1-q)^2 W_N
--     ~= q - (N+1)q^(N+1) + Nq^(N+2)
--
-- and 0 <= q < 1, the correction
--
--   (N+1)q^(N+1) - Nq^(N+2)
--
-- is nonnegative.  Hence every finite partial sum satisfies
--
--   W_N <= q / (1-q)^2.
--
-- This is finite and constructive; it does not pass to an infinite weighted
-- series and does not require an exponential addition theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base as ℤ using (+_)
import Data.Nat.Properties as ℕP
open import Data.Rational.Unnormalised as ℚ using (0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as ℚP
open import Data.Sum.Base using (inj₂)

import Inverse as BishopInverse
import Real as BishopReal
import RealProperties as BishopP
import Sequence as BishopSequence

import DASHI.Foundations.BishopFiniteDegreeOneGeometricIdentityExact as Identity
import DASHI.Mathematics.NumberTheory.FiniteNatRationalEmbeddingExact as NatEmbed
open import DASHI.Physics.YangMills.CompactLieProofLevel

natRealNonnegative : ∀ n →
  BishopReal.NonNegative (Identity.natReal n)
natRealNonnegative n =
  BishopP.0≤x⇒nonNegx
    (BishopP.p≤q⇒p⋆≤q⋆
      0ℚᵘ
      (NatEmbed.natAsRational n)
      (ℚP.nonNegative⁻¹ (NatEmbed.natAsRational n)))

natRealBelowSuccessor : ∀ n →
  BishopReal._≤_ (Identity.natReal n) (Identity.natReal (suc n))
natRealBelowSuccessor n =
  BishopP.p≤q⇒p⋆≤q⋆
    (NatEmbed.natAsRational n)
    (NatEmbed.natAsRational (suc n))
    (ℚ.*≤* (ℤ.+≤+ (ℕP.n≤1+n n)))

record BishopUnitIntervalRatio (q : BishopReal.ℝ) : Set₁ where
  field
    ratioNonnegative : BishopReal._≤_ BishopReal.0ℝ q
    ratioBelowOne : BishopReal._<_ q BishopReal.1ℝ

open BishopUnitIntervalRatio public

ratioNonnegativeWitness :
  ∀ {q} → BishopUnitIntervalRatio q → BishopReal.NonNegative q
ratioNonnegativeWitness inputs =
  BishopP.0≤x⇒nonNegx (ratioNonnegative inputs)

ratioPowerNonnegative :
  ∀ {q} → BishopUnitIntervalRatio q →
  ∀ exponent → BishopReal.NonNegative (BishopReal.pow q exponent)
ratioPowerNonnegative inputs exponent =
  BishopSequence.nonNegx⇒nonNegxⁿ exponent
    (ratioNonnegativeWitness inputs)

nTimesRatioBelowSuccessor :
  ∀ {q} → BishopUnitIntervalRatio q →
  ∀ n →
  BishopReal._≤_
    (BishopReal._*_ (Identity.natReal n) q)
    (Identity.natReal (suc n))
nTimesRatioBelowSuccessor {q} inputs n =
  BishopP.≤-trans
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityʳ (Identity.natReal n))
      (BishopP.*-monoˡ-≤-nonNeg
        (BishopP.<⇒≤ (ratioBelowOne inputs))
        (natRealNonnegative n)))
    (natRealBelowSuccessor n)

correction : BishopReal.ℝ → Nat → BishopReal.ℝ
correction q count =
  BishopReal._-_
    (BishopReal._*_
      (Identity.natReal (suc count))
      (BishopReal.pow q (suc count)))
    (BishopReal._*_
      (Identity.natReal count)
      (BishopReal.pow q (suc (suc count))))

correctionFactorization :
  (q : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (correction q count)
    (BishopReal._*_
      (BishopReal.pow q (suc count))
      (BishopReal._-_
        (Identity.natReal (suc count))
        (BishopReal._*_ (Identity.natReal count) q)))
correctionFactorization q count =
  let
    p = BishopReal.pow q (suc count)
    n = Identity.natReal count
    next = Identity.natReal (suc count)
    open BishopP.ℝ-Solver
  in
  solve 4
    (λ q′ p′ n′ next′ →
      (next′ ⊗ p′) ⊖ (n′ ⊗ (p′ ⊗ q′))
      ⊜ p′ ⊗ (next′ ⊖ (n′ ⊗ q′)))
    BishopP.≃-refl q p n next

correctionNonnegative :
  ∀ {q} → BishopUnitIntervalRatio q →
  ∀ count → BishopReal.NonNegative (correction q count)
correctionNonnegative {q} inputs count =
  let
    pNonnegative = ratioPowerNonnegative inputs (suc count)
    bracketOrder = nTimesRatioBelowSuccessor inputs count
    bracketNonnegative =
      BishopP.0≤x⇒nonNegx
        (BishopSequence.x≤y⇒0≤y-x bracketOrder)
    productNonnegative =
      BishopP.nonNegx,y⇒nonNegx*y
        pNonnegative bracketNonnegative
  in
  BishopP.nonNeg-cong
    (BishopP.≃-symm (correctionFactorization q count))
    productNonnegative

identityRightIsQMinusCorrection :
  (q : BishopReal.ℝ) →
  ∀ count →
  BishopReal._≃_
    (BishopReal._+_
      (BishopReal._-_
        q
        (BishopReal._*_
          (Identity.natReal (suc count))
          (BishopReal.pow q (suc count))))
      (BishopReal._*_
        (Identity.natReal count)
        (BishopReal.pow q (suc (suc count)))))
    (BishopReal._-_ q (correction q count))
identityRightIsQMinusCorrection q count =
  let
    a = BishopReal._*_
      (Identity.natReal (suc count))
      (BishopReal.pow q (suc count))
    b = BishopReal._*_
      (Identity.natReal count)
      (BishopReal.pow q (suc (suc count)))
    open BishopP.ℝ-Solver
  in
  solve 3
    (λ q′ a′ b′ →
      (q′ ⊖ a′) ⊕ b′ ⊜ q′ ⊖ (a′ ⊖ b′))
    BishopP.≃-refl q a b

qMinusCorrectionBelowQ :
  ∀ {q} → BishopUnitIntervalRatio q →
  ∀ count →
  BishopReal._≤_
    (BishopReal._-_ q (correction q count))
    q
qMinusCorrectionBelowQ {q} inputs count =
  let
    corr = correction q count
    corrOrder = BishopP.nonNegx⇒0≤x (correctionNonnegative inputs count)
    raw = BishopP.+-monoʳ-≤ q (BishopP.neg-mono-≤ corrOrder)
    open BishopP.ℝ-Solver
  in
  BishopP.≤-respʳ-≃
    (solve 1
      (λ q′ → q′ ⊕ (⊝ Κ 0ℚᵘ) ⊜ q′)
      BishopP.≃-refl q)
    raw

scaledWeightedPartialBelowRatio :
  ∀ {q} → BishopUnitIntervalRatio q →
  ∀ count →
  BishopReal._≤_
    (BishopReal._*_
      (Identity.square (Identity.oneMinus q))
      (Identity.weightedPartial q count))
    q
scaledWeightedPartialBelowRatio {q} inputs count =
  let
    scaledToRight =
      BishopP.≃-trans
        (Identity.finiteDegreeOneGeometricIdentity q count)
        (identityRightIsQMinusCorrection q count)
  in
  BishopP.≤-respˡ-≃
    (BishopP.≃-symm scaledToRight)
    (qMinusCorrectionBelowQ inputs count)

oneMinusPositive :
  ∀ {q} → BishopUnitIntervalRatio q →
  BishopReal._<_ BishopReal.0ℝ (Identity.oneMinus q)
oneMinusPositive {q} inputs =
  BishopP.x<y⇒0<y-x q BishopReal.1ℝ (ratioBelowOne inputs)

oneMinusNonzero :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) →
  BishopReal._≄0 (Identity.oneMinus q)
oneMinusNonzero inputs = inj₂ (oneMinusPositive inputs)

oneMinusInverse :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) → BishopReal.ℝ
oneMinusInverse {q} inputs =
  BishopInverse._⁻¹ (Identity.oneMinus q) (oneMinusNonzero inputs)

oneMinusInverseNonnegative :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) →
  BishopReal.NonNegative (oneMinusInverse inputs)
oneMinusInverseNonnegative inputs =
  BishopP.0≤x⇒nonNegx
    (BishopP.<⇒≤
      (BishopInverse.0<x⇒0<x⁻¹
        (oneMinusNonzero inputs)
        (oneMinusPositive inputs)))

inverseSquareNonnegative :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) →
  BishopReal.NonNegative
    (BishopReal._*_
      (oneMinusInverse inputs)
      (oneMinusInverse inputs))
inverseSquareNonnegative inputs =
  BishopP.nonNegx,y⇒nonNegx*y
    (oneMinusInverseNonnegative inputs)
    (oneMinusInverseNonnegative inputs)

inverseSquareCancelsGapSquare :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) →
  ∀ value →
  BishopReal._≃_
    (BishopReal._*_
      (BishopReal._*_
        (oneMinusInverse inputs)
        (oneMinusInverse inputs))
      (BishopReal._*_
        (Identity.square (Identity.oneMinus q))
        value))
    value
inverseSquareCancelsGapSquare {q} inputs value =
  let
    gap = Identity.oneMinus q
    inverse = oneMinusInverse inputs
    inverseLaw = BishopInverse.*-inverseˡ gap (oneMinusNonzero inputs)
    open BishopP.ℝ-Solver
    reassociate :
      BishopReal._≃_
        (BishopReal._*_
          (BishopReal._*_ inverse inverse)
          (BishopReal._*_ (BishopReal._*_ gap gap) value))
        (BishopReal._*_
          (BishopReal._*_ inverse gap)
          (BishopReal._*_
            (BishopReal._*_ inverse gap)
            value))
    reassociate =
      solve 3
        (λ i g v →
          (i ⊗ i) ⊗ ((g ⊗ g) ⊗ v)
          ⊜ (i ⊗ g) ⊗ ((i ⊗ g) ⊗ v))
        BishopP.≃-refl inverse gap value
  in
  BishopP.≃-trans reassociate
    (BishopP.≃-trans
      (BishopP.*-cong
        inverseLaw
        (BishopP.*-congʳ inverseLaw))
      (let open BishopP.ℝ-Solver
       in solve 1
          (λ v → Κ 1ℚᵘ ⊗ (Κ 1ℚᵘ ⊗ v) ⊜ v)
          BishopP.≃-refl value))

finiteDegreeOneGeometricBound :
  ∀ {q} (inputs : BishopUnitIntervalRatio q) →
  ∀ count →
  BishopReal._≤_
    (Identity.weightedPartial q count)
    (BishopReal._*_
      q
      (BishopReal._*_
        (oneMinusInverse inputs)
        (oneMinusInverse inputs)))
finiteDegreeOneGeometricBound {q} inputs count =
  let
    inverseSquare =
      BishopReal._*_
        (oneMinusInverse inputs)
        (oneMinusInverse inputs)
    scaled =
      BishopP.*-monoˡ-≤-nonNeg
        (scaledWeightedPartialBelowRatio inputs count)
        (inverseSquareNonnegative inputs)
    leftCancel =
      inverseSquareCancelsGapSquare inputs
        (Identity.weightedPartial q count)
    rightCommute =
      BishopP.*-comm inverseSquare q
  in
  BishopP.≤-respʳ-≃ rightCommute
    (BishopP.≤-respˡ-≃ leftCancel scaled)

bishopFiniteDegreeOneGeometricBoundLevel : ProofLevel
bishopFiniteDegreeOneGeometricBoundLevel = machineChecked
