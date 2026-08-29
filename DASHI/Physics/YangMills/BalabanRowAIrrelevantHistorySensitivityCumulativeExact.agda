module DASHI.Physics.YangMills.BalabanRowAIrrelevantHistorySensitivityCumulativeExact where

------------------------------------------------------------------------
-- ROW A: CONTRACTIVE IRRELEVANT MEMORY -> EXPLICIT CUMULATIVE q_history
--
-- The existing irrelevant-memory theorem gives
--
--   deltaBeta_d <= L D0 2^-d.
--
-- The exact dyadic partial sum is < 2, so every finite cumulative history
-- response is bounded by 2 L D0.  If the initial irrelevant displacement obeys
--
--   D0 <= S |delta u|,
--
-- then
--
--   Sum_d deltaBeta_d <= (2 L S) |delta u|.
--
-- This is precisely the history constant needed by the additive Row-A
-- sensitivity split.  The marginal running coupling is not included here.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanIrrelevantRGMemoryContractionExact as Memory
import DASHI.Physics.YangMills.BalabanTraceKoteckyPreissGeometricExact as Geo
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

sumBetaDifference : (Nat → ℚ) → Nat → ℚ
sumBetaDifference beta zero = 0ℚ
sumBetaDifference beta (suc n) = sumBetaDifference beta n + beta n

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
    amplitudeNN =
      let
        instance
          lNN = ℚ.nonNegative (Memory.lipschitzNonnegative projection)
          dNN = ℚ.nonNegative (Memory.initialDistanceNonnegative memory)
      in
      ℚP.nonNegative⁻¹ (L * D)

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

-- Physical seam: identify D0 as the literal irrelevant/polymer displacement
-- generated by a change in the initial inverse coupling and prove the source
-- response coefficient S on the same admissible tube.
literalIrrelevantHistoryInitialResponseToInverseSquareInputLevel : ProofLevel
literalIrrelevantHistoryInitialResponseToInverseSquareInputLevel = conditional
