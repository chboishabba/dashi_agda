module DASHI.Physics.Closure.NSTriadKNLuoResidualSourceLedgerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Michel Bony,
-- "Calcul symbolique et propagation des singularites pour les equations
-- aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Roger Temam,
-- "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The seven residual sources named by the highest-alpha continuation plan
-- are represented literally:
--
--   collar, tail, pressure, low, phase, passive, fragmentation.
--
-- The weighted finite residual is proved equal to the sum of the seven
-- weighted component ledgers.  Componentwise budgets therefore imply the
-- exact combined budget.  No source is hidden under the words lower order,
-- perturbative, bounded overlap, or harmless.
--
-- This closes the finite bookkeeping demanded by NS-F.  Producing each
-- component budget from the physical Navier-Stokes localization remains the
-- analytic obligation.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

record ResidualCell : Set where
  constructor residualCell
  field
    weight : ℚ
    collar : ℚ
    tail : ℚ
    pressure : ℚ
    low : ℚ
    phase : ℚ
    passive : ℚ
    fragmentation : ℚ

open ResidualCell public

sumSeven : ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ → ℚ
sumSeven a b c d e f g = ((((((a + b) + c) + d) + e) + f) + g)

totalResidual : ResidualCell → ℚ
totalResidual cell =
  sumSeven
    (collar cell)
    (tail cell)
    (pressure cell)
    (low cell)
    (phase cell)
    (passive cell)
    (fragmentation cell)

weightedSum : (ResidualCell → ℚ) → List ResidualCell → ℚ
weightedSum select [] = 0ℚ
weightedSum select (cell ∷ cells) =
  weight cell * select cell + weightedSum select cells

weightedTotalResidual : List ResidualCell → ℚ
weightedTotalResidual = weightedSum totalResidual

weightedCollar : List ResidualCell → ℚ
weightedCollar = weightedSum collar

weightedTail : List ResidualCell → ℚ
weightedTail = weightedSum tail

weightedPressure : List ResidualCell → ℚ
weightedPressure = weightedSum pressure

weightedLow : List ResidualCell → ℚ
weightedLow = weightedSum low

weightedPhase : List ResidualCell → ℚ
weightedPhase = weightedSum phase

weightedPassive : List ResidualCell → ℚ
weightedPassive = weightedSum passive

weightedFragmentation : List ResidualCell → ℚ
weightedFragmentation = weightedSum fragmentation

residualLedgerDecomposition :
  ∀ cells →
  weightedTotalResidual cells
  ≡
  sumSeven
    (weightedCollar cells)
    (weightedTail cells)
    (weightedPressure cells)
    (weightedLow cells)
    (weightedPhase cells)
    (weightedPassive cells)
    (weightedFragmentation cells)
residualLedgerDecomposition [] = solve []
residualLedgerDecomposition (cell ∷ cells)
  rewrite residualLedgerDecomposition cells =
  solve
    ( weight cell
    ∷ collar cell
    ∷ tail cell
    ∷ pressure cell
    ∷ low cell
    ∷ phase cell
    ∷ passive cell
    ∷ fragmentation cell
    ∷ weightedCollar cells
    ∷ weightedTail cells
    ∷ weightedPressure cells
    ∷ weightedLow cells
    ∷ weightedPhase cells
    ∷ weightedPassive cells
    ∷ weightedFragmentation cells
    ∷ [])

sumSevenMonotone :
  ∀ {a₁ a₂ a₃ a₄ a₅ a₆ a₇ b₁ b₂ b₃ b₄ b₅ b₆ b₇} →
  a₁ ≤ b₁ →
  a₂ ≤ b₂ →
  a₃ ≤ b₃ →
  a₄ ≤ b₄ →
  a₅ ≤ b₅ →
  a₆ ≤ b₆ →
  a₇ ≤ b₇ →
  sumSeven a₁ a₂ a₃ a₄ a₅ a₆ a₇
  ≤ sumSeven b₁ b₂ b₃ b₄ b₅ b₆ b₇
sumSevenMonotone p₁ p₂ p₃ p₄ p₅ p₆ p₇ =
  ℚₚ.+-mono-≤
    (ℚₚ.+-mono-≤
      (ℚₚ.+-mono-≤
        (ℚₚ.+-mono-≤
          (ℚₚ.+-mono-≤
            (ℚₚ.+-mono-≤ p₁ p₂)
            p₃)
          p₄)
        p₅)
      p₆)
    p₇

record ResidualComponentBudgets (cells : List ResidualCell) : Set where
  constructor residualComponentBudgets
  field
    collarBudget : ℚ
    tailBudget : ℚ
    pressureBudget : ℚ
    lowBudget : ℚ
    phaseBudget : ℚ
    passiveBudget : ℚ
    fragmentationBudget : ℚ

    collarWithinBudget : weightedCollar cells ≤ collarBudget
    tailWithinBudget : weightedTail cells ≤ tailBudget
    pressureWithinBudget : weightedPressure cells ≤ pressureBudget
    lowWithinBudget : weightedLow cells ≤ lowBudget
    phaseWithinBudget : weightedPhase cells ≤ phaseBudget
    passiveWithinBudget : weightedPassive cells ≤ passiveBudget
    fragmentationWithinBudget :
      weightedFragmentation cells ≤ fragmentationBudget

open ResidualComponentBudgets public

combinedResidualBudget :
  ∀ {cells} → ResidualComponentBudgets cells → ℚ
combinedResidualBudget budgets =
  sumSeven
    (collarBudget budgets)
    (tailBudget budgets)
    (pressureBudget budgets)
    (lowBudget budgets)
    (phaseBudget budgets)
    (passiveBudget budgets)
    (fragmentationBudget budgets)

weightedTotalResidualWithinCombinedBudget :
  ∀ {cells} (budgets : ResidualComponentBudgets cells) →
  weightedTotalResidual cells ≤ combinedResidualBudget budgets
weightedTotalResidualWithinCombinedBudget {cells} budgets =
  let
    componentwise :
      sumSeven
        (weightedCollar cells)
        (weightedTail cells)
        (weightedPressure cells)
        (weightedLow cells)
        (weightedPhase cells)
        (weightedPassive cells)
        (weightedFragmentation cells)
      ≤ combinedResidualBudget budgets
    componentwise =
      sumSevenMonotone
        (collarWithinBudget budgets)
        (tailWithinBudget budgets)
        (pressureWithinBudget budgets)
        (lowWithinBudget budgets)
        (phaseWithinBudget budgets)
        (passiveWithinBudget budgets)
        (fragmentationWithinBudget budgets)
  in
  subst
    (λ left → left ≤ combinedResidualBudget budgets)
    (sym (residualLedgerDecomposition cells))
    componentwise

record ResidualLedgerAuthorityBoundary : Set where
  constructor residualLedgerAuthorityBoundary
  field
    finiteLedgerIdentityProved : Set
    componentBudgetsProducedFromPhysicalLocalization : Set
    infiniteCriticalWeightedSummabilityProved : Set

canonicalResidualLedgerAuthorityBoundary :
  ResidualLedgerAuthorityBoundary
canonicalResidualLedgerAuthorityBoundary =
  residualLedgerAuthorityBoundary
    ⊤
    ⊥
    ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
