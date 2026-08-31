module DASHI.Physics.YangMills.BalabanRowAIrrelevantHistorySensitivityCumulativeExact where

------------------------------------------------------------------------
-- ROW A: CONTRACTIVE IRRELEVANT MEMORY -> EXPLICIT CUMULATIVE q_history
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _*_; _≤_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact as Memory
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

mulNN : ∀ {left right} → 0ℚ ≤ left → 0ℚ ≤ right → 0ℚ ≤ left * right
mulNN {left} {right} leftNN rightNN =
  let
    instance
      leftNonnegative : NonNegative left
      leftNonnegative = ℚ.nonNegative leftNN
      rightNonnegative : NonNegative right
      rightNonnegative = ℚ.nonNegative rightNN
  in
  ℚP.nonNegative⁻¹ (left * right)

sumBetaDifference : (Nat → ℚ) → Nat → ℚ
sumBetaDifference beta zero = 0ℚ
sumBetaDifference beta (suc n) = sumBetaDifference beta n + beta n

sumBetaDifferenceNonnegative :
  ∀ {memory}
    (projection : Memory.LipschitzIrrelevantBetaProjection memory) →
  ∀ K → 0ℚ ≤ sumBetaDifference (Memory.betaDifference projection) K
sumBetaDifferenceNonnegative projection zero = ℚP.≤-refl
sumBetaDifferenceNonnegative projection (suc n) =
  ℚP.+-mono-≤
    (sumBetaDifferenceNonnegative projection n)
    (Memory.betaDifferenceNonnegative projection n)

cumulativeIrrelevantMemoryBelowPartialGeometric :
  ∀ {memory}
    (projection : Memory.LipschitzIrrelevantBetaProjection memory) →
  ∀ K →
  sumBetaDifference (Memory.betaDifference projection) K
  ≤ (Memory.lipschitzConstant projection * Memory.initialDistance memory)
      * Geo.traceShellPartialSum K
cumulativeIrrelevantMemoryBelowPartialGeometric {memory} projection zero =
  subst (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀
      (Memory.lipschitzConstant projection)
      (Memory.initialDistance memory))
    ℚP.≤-refl
cumulativeIrrelevantMemoryBelowPartialGeometric {memory} projection (suc n) =
  let
    induction = cumulativeIrrelevantMemoryBelowPartialGeometric projection n
    current = Memory.betaIrrelevantMemoryBelowDyadic projection n
    added = ℚP.+-mono-≤ induction current
  in
  subst
    (λ upper →
      sumBetaDifference (Memory.betaDifference projection) (suc n) ≤ upper)
    (ℚRing.solve-∀
      (Memory.lipschitzConstant projection)
      (Memory.initialDistance memory)
      (Geo.traceShellPartialSum n)
      (Geo.halfPower n))
    added

cumulativeIrrelevantMemoryBelowTwiceInitial :
  ∀ {memory}
    (projection : Memory.LipschitzIrrelevantBetaProjection memory) →
  ∀ K →
  sumBetaDifference (Memory.betaDifference projection) K
  ≤ Geo.twoℚ
      * (Memory.lipschitzConstant projection * Memory.initialDistance memory)
cumulativeIrrelevantMemoryBelowTwiceInitial {memory} projection K =
  let
    L = Memory.lipschitzConstant projection
    D = Memory.initialDistance memory

    amplitudeNN : 0ℚ ≤ L * D
    amplitudeNN = mulNN
      (Memory.lipschitzNonnegative projection)
      (Memory.initialDistanceNonnegative memory)

    scaledGeometric =
      Norm.scaleNonnegative
        (L * D) amplitudeNN
        (Geo.traceShellPartialSumBelowTwo K)
  in
  ℚP.≤-trans
    (cumulativeIrrelevantMemoryBelowPartialGeometric projection K)
    (subst
      (λ upper →
        (L * D) * Geo.traceShellPartialSum K ≤ upper)
      (ℚRing.solve-∀ L D Geo.twoℚ)
      scaledGeometric)

record IrrelevantHistoryInputResponse
    {memory : Memory.ContractiveIrrelevantMemory}
    (projection : Memory.LipschitzIrrelevantBetaProjection memory) : Set₁ where
  field
    inputDistance responseConstant : ℚ
    inputDistanceNonnegative : 0ℚ ≤ inputDistance
    responseConstantNonnegative : 0ℚ ≤ responseConstant
    initialDistanceBelowInput :
      Memory.initialDistance memory ≤ responseConstant * inputDistance

open IrrelevantHistoryInputResponse public

historySensitivityConstant :
  ∀ {memory}
    {projection : Memory.LipschitzIrrelevantBetaProjection memory} →
  IrrelevantHistoryInputResponse projection → ℚ
historySensitivityConstant {projection = projection} response =
  Geo.twoℚ * Memory.lipschitzConstant projection * responseConstant response

historySensitivityConstantNonnegative :
  ∀ {memory}
    {projection : Memory.LipschitzIrrelevantBetaProjection memory}
    (response : IrrelevantHistoryInputResponse projection) →
  0ℚ ≤ historySensitivityConstant response
historySensitivityConstantNonnegative {projection = projection} response =
  let
    twoNN : 0ℚ ≤ Geo.twoℚ
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof
  in
  mulNN
    (mulNN twoNN (Memory.lipschitzNonnegative projection))
    (responseConstantNonnegative response)

cumulativeIrrelevantHistorySensitivity :
  ∀ {memory}
    {projection : Memory.LipschitzIrrelevantBetaProjection memory}
    (response : IrrelevantHistoryInputResponse projection) →
  ∀ K →
  sumBetaDifference (Memory.betaDifference projection) K
  ≤ historySensitivityConstant response * inputDistance response
cumulativeIrrelevantHistorySensitivity {memory} {projection} response K =
  let
    L = Memory.lipschitzConstant projection
    D = Memory.initialDistance memory
    S = responseConstant response
    d = inputDistance response

    lScaled : L * D ≤ L * (S * d)
    lScaled = Norm.scaleNonnegative
      L (Memory.lipschitzNonnegative projection)
      (initialDistanceBelowInput response)

    twoNN : 0ℚ ≤ Geo.twoℚ
    twoNN = ℚP.+-mono-≤ Geo.oneNonnegativeProof Geo.oneNonnegativeProof

    twiceScaled :
      Geo.twoℚ * (L * D) ≤ Geo.twoℚ * (L * (S * d))
    twiceScaled = Norm.scaleNonnegative Geo.twoℚ twoNN lScaled
  in
  ℚP.≤-trans
    (cumulativeIrrelevantMemoryBelowTwiceInitial projection K)
    (subst
      (λ upper → Geo.twoℚ * (L * D) ≤ upper)
      (ℚRing.solve-∀ Geo.twoℚ L S d)
      twiceScaled)

rowAIrrelevantHistoryDyadicSummationLevel : ProofLevel
rowAIrrelevantHistoryDyadicSummationLevel = machineChecked

rowAIrrelevantHistoryInputSensitivityLevel : ProofLevel
rowAIrrelevantHistoryInputSensitivityLevel = machineChecked

literalIrrelevantHistoryInitialResponseToInverseSquareInputLevel : ProofLevel
literalIrrelevantHistoryInitialResponseToInverseSquareInputLevel = conditional
