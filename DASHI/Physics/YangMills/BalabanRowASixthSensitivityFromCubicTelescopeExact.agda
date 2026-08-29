module DASHI.Physics.YangMills.BalabanRowASixthSensitivityFromCubicTelescopeExact where

------------------------------------------------------------------------
-- ROW A: SIXTH-ORDER SENSITIVITY SUM FROM THE EXISTING CUBIC COUPLING TELESCOPE
--
-- The inverse-square chain rule reduction produces per-shell direct sensitivity
-- of order g_j^6.  The repository already proves a finite-cutoff cubic telescope
-- from the same positive inverse-square beta margin.  On a small-coupling tube
-- 0 <= g_j <= gamma,
--
--       g_j^6 <= gamma^3 g_j^3.
--
-- Hence the cubic telescope automatically controls the entire sixth-order
-- sensitivity sum.  This is exact rational algebra and introduces no new
-- history-decay hypothesis.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4CubicCouplingDriftTelescopeExact as Cubic

cube : ℚ → ℚ
cube g = (g * g) * g

sixth : ℚ → ℚ
sixth g = cube g * cube g

sumSixth : (Nat → ℚ) → Nat → ℚ
sumSixth g zero = 0ℚ
sumSixth g (suc n) = sumSixth g n + sixth (g n)

cubeMonotoneNonnegative : ∀ {lower upper} →
  0ℚ ≤ lower → 0ℚ ≤ upper → lower ≤ upper →
  cube lower ≤ cube upper
cubeMonotoneNonnegative {lower} {upper} lowerNN upperNN lowerBelow =
  let
    lowerSquareNN = Cubic.productNonnegative lower lower lowerNN lowerNN
    upperSquareNN = Cubic.productNonnegative upper upper upperNN upperNN

    squareBelow : lower * lower ≤ upper * upper
    squareBelow = ℚP.*-mono-≤ lowerNN lowerBelow lowerNN lowerBelow
  in
  ℚP.*-mono-≤ lowerSquareNN squareBelow lowerNN lowerBelow

sixthBelowGammaCubeTimesCube : ∀ {g gamma} →
  0ℚ ≤ g → 0ℚ ≤ gamma → g ≤ gamma →
  sixth g ≤ cube gamma * cube g
sixthBelowGammaCubeTimesCube {g} {gamma} gNN gammaNN gBelow =
  let
    gCubeNN = Cubic.productNonnegative (g * g) g
      (Cubic.productNonnegative g g gNN gNN) gNN
    cubeBelow = cubeMonotoneNonnegative gNN gammaNN gBelow
  in
  Cubic.scaleʳ-nonNeg gCubeNN cubeBelow

sumSixthBelowGammaCubeTimesSumCubes :
  (g : Nat → ℚ) (gamma : ℚ) →
  0ℚ ≤ gamma →
  (∀ j → 0ℚ ≤ g j) →
  (∀ j → g j ≤ gamma) →
  ∀ K →
  sumSixth g K ≤ cube gamma * Cubic.sumCubes g K
sumSixthBelowGammaCubeTimesSumCubes g gamma gammaNN gNN gBelow zero =
  subst (λ right → 0ℚ ≤ right)
    (ℚRing.solve-∀ gamma) ℚP.≤-refl
sumSixthBelowGammaCubeTimesSumCubes g gamma gammaNN gNN gBelow (suc n) =
  let
    induction = sumSixthBelowGammaCubeTimesSumCubes
      g gamma gammaNN gNN gBelow n

    current = sixthBelowGammaCubeTimesCube
      (gNN n) gammaNN (gBelow n)

    added = ℚP.+-mono-≤ induction current
  in
  subst
    (λ upper → sumSixth g (suc n) ≤ upper)
    (ℚRing.solve-∀ gamma (Cubic.sumCubes g n) (cube (g n)))
    added

module FromFlow {cutoff : Nat}
    (flow : Cubic.InverseSquareMarginFlow cutoff) where

  sixthSensitivityBudgetInTube :
    0ℚ ≤ Cubic.marginConstant flow →
    ∀ {gamma tubeWidth} →
    0ℚ ≤ gamma →
    (∀ j → 0ℚ ≤ Cubic.coupling flow j) →
    (∀ j → Cubic.coupling flow j ≤ gamma) →
    (∀ K → Cubic.coupling flow K - Cubic.coupling flow zero ≤ tubeWidth) →
    ∀ K → K Data.Nat.Base.≤ cutoff →
    Cubic.marginConstant flow * sumSixth (Cubic.coupling flow) K
      ≤ (Cubic.twoℚ * cube gamma) * tubeWidth
  sixthSensitivityBudgetInTube marginNN {gamma} {tubeWidth}
      gammaNN couplingNN couplingBelow tube K K≤ =
    let
      sixthToCubic = sumSixthBelowGammaCubeTimesSumCubes
        (Cubic.coupling flow) gamma gammaNN couplingNN couplingBelow K

      scaledSixth = Cubic.scaleˡ-nonNeg marginNN sixthToCubic

      cubicBudget = Cubic.Flow.cubicSumInTube flow marginNN tube K K≤

      gammaCubeNN = Cubic.productNonnegative (gamma * gamma) gamma
        (Cubic.productNonnegative gamma gamma gammaNN gammaNN) gammaNN

      scaledCubic = Cubic.scaleˡ-nonNeg gammaCubeNN cubicBudget
    in
    ℚP.≤-trans
      scaledSixth
      (subst
        (λ upper →
          Cubic.marginConstant flow * (cube gamma * Cubic.sumCubes (Cubic.coupling flow) K)
          ≤ upper)
        (ℚRing.solve-∀
          (Cubic.marginConstant flow)
          (Cubic.sumCubes (Cubic.coupling flow) K)
          gamma tubeWidth)
        scaledCubic)

rowASixthFromCubicTubeAlgebraLevel : ProofLevel
rowASixthFromCubicTubeAlgebraLevel = machineChecked

-- Physical use: instantiate the same small-coupling tube and the same positive
-- inverse-square margin with the literal Row-A trajectory, then multiply this
-- sixth-order sum by the source-derived direct channel sensitivity constant.
literalRowASixthSensitivityTubeInstantiationLevel : ProofLevel
literalRowASixthSensitivityTubeInstantiationLevel = conditional
