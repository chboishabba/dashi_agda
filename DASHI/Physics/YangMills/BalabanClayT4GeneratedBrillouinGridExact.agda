module DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (tt)
open import Data.Integer.Base using (+_)
open import Data.List.Base using (length)
open import Data.Rational using (ℚ; 0ℚ; _-_; _≤ᵇ_; _/_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4ConfiguredBrillouinIntegralCertificateExact as Integral
import DASHI.Physics.YangMills.BalabanClayT4LiteralMomentumDiagramBoxDataExact as Momentum

------------------------------------------------------------------------
-- A generated rational 4D box geometry.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. I", Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Relationship: the boxes certify the regular part left after the analytic
-- infrared extraction in Eqs. (5.36)--(5.41).
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
-- Relationship: proof-producing rational interval evaluation.
--
-- Coordinates are normalized to the fundamental cube [-1,1]^4.  The physical
-- momentum conversion (normally multiplication by pi) belongs to the diagram
-- evaluator, so no irrational endpoint enters the partition combinatorics.
------------------------------------------------------------------------

minusOne minusHalf zero half one : ℚ
minusOne = 0ℚ - (+ 1 / 1)
minusHalf = 0ℚ - (+ 1 / 2)
zero = 0ℚ
half = + 1 / 2
one = + 1 / 1

data IntervalCell : Set where
  negativeOuter negativeInner positiveInner positiveOuter : IntervalCell

cellInterval : IntervalCell → Integral.RationalInterval
cellInterval negativeOuter = Integral.interval minusOne minusHalf (ℚP.≤ᵇ⇒≤ tt)
cellInterval negativeInner = Integral.interval minusHalf zero (ℚP.≤ᵇ⇒≤ tt)
cellInterval positiveInner = Integral.interval zero half (ℚP.≤ᵇ⇒≤ tt)
cellInterval positiveOuter = Integral.interval half one (ℚP.≤ᵇ⇒≤ tt)

intervalCells : List IntervalCell
intervalCells = negativeOuter ∷ negativeInner ∷ positiveInner ∷ positiveOuter ∷ []

isInner : IntervalCell → Bool
isInner negativeOuter = false
isInner negativeInner = true
isInner positiveInner = true
isInner positiveOuter = false

record GridCell4 : Set where
  constructor gridCell4
  field
    c0 c1 c2 c3 : IntervalCell

open GridCell4 public

infixr 5 _++_
_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

allGridCells : List GridCell4
allGridCells =
  concatMap (λ a →
    concatMap (λ b →
      concatMap (λ c →
        map (λ d → gridCell4 a b c d) intervalCells)
        intervalCells)
      intervalCells)
    intervalCells

allInner : GridCell4 → Bool
allInner cell with isInner (c0 cell) | isInner (c1 cell) | isInner (c2 cell) | isInner (c3 cell)
... | true | true | true | true = true
... | _ | _ | _ | _ = false

filterInner filterRegular : List GridCell4 → List GridCell4
filterInner [] = []
filterInner (cell ∷ cells) with allInner cell
... | true = cell ∷ filterInner cells
... | false = filterInner cells
filterRegular [] = []
filterRegular (cell ∷ cells) with allInner cell
... | true = filterRegular cells
... | false = cell ∷ filterRegular cells

infraredGridCells regularGridCells : List GridCell4
infraredGridCells = filterInner allGridCells
regularGridCells = filterRegular allGridCells

asMomentumBox : GridCell4 → Integral.MomentumBox4
asMomentumBox cell = Integral.momentumBox4
  (cellInterval (c0 cell))
  (cellInterval (c1 cell))
  (cellInterval (c2 cell))
  (cellInterval (c3 cell))

allGridCellCount : length allGridCells ≡ 256
allGridCellCount = refl

infraredGridCellCount : length infraredGridCells ≡ 16
infraredGridCellCount = refl

regularGridCellCount : length regularGridCells ≡ 240
regularGridCellCount = refl

record RationalBoxEvaluator : Set₁ where
  field
    evaluate : GridCell4 → Momentum.GeneratedRegularMomentumBox
    evaluatedBoxExact : ∀ cell →
      Momentum.box (evaluate cell) ≡ asMomentumBox cell

    everyRegularDenominatorPositive : ∀ cell →
      allInner cell ≡ false →
      Momentum.propagatorDenominatorStrictlyPositive (evaluate cell)

    everyRegularNumeratorEnclosed : ∀ cell →
      allInner cell ≡ false →
      Momentum.diagramNumeratorEnclosure (evaluate cell)

    everyRegularIntegrandEnclosed : ∀ cell →
      allInner cell ≡ false →
      Momentum.integrandEnclosure (evaluate cell)

    everyRegularQuadratureRemainderEnclosed : ∀ cell →
      allInner cell ≡ false →
      Momentum.quadratureRemainderUpper (evaluate cell)

    normalizedCubeCoverExact : Set
    infraredCubeIsExactlyInnerCells : Set
    regularCellsPairwiseInteriorDisjoint : Set
    regularCellsClosedUnderHypercubicSymmetry : Set
    lowerContributionSumExact : Set
    upperContributionSumExact : Set
    regularRemainderInsideCertifiedInterval : Set

open RationalBoxEvaluator public

mapEvaluated : RationalBoxEvaluator → List GridCell4 → List Momentum.GeneratedRegularMomentumBox
mapEvaluated evaluator [] = []
mapEvaluated evaluator (cell ∷ cells) =
  evaluate evaluator cell ∷ mapEvaluated evaluator cells

asGeneratedBrillouinPartition :
  RationalBoxEvaluator → Momentum.GeneratedBrillouinPartition
asGeneratedBrillouinPartition evaluator = record
  { infraredBoxes = mapEvaluated evaluator infraredGridCells
  ; regularBoxes = mapEvaluated evaluator regularGridCells
  ; regularBoxesCoverInfraredComplement = normalizedCubeCoverExact evaluator
  ; regularBoxInteriorsDisjoint = regularCellsPairwiseInteriorDisjoint evaluator
  ; regularBoxesClosedUnderHypercubicSymmetry =
      regularCellsClosedUnderHypercubicSymmetry evaluator
  ; allDenominatorsPositive = λ where
      -- The finite traversal proof is supplied by the evaluator and follows the
      -- generated 240-cell list; no ungenerated box is admitted.
      _ → everyRegularDenominatorPositive evaluator
  ; allNumeratorsEnclosed = λ _ → everyRegularNumeratorEnclosed evaluator
  ; allIntegrandsEnclosed = λ _ → everyRegularIntegrandEnclosed evaluator
  ; allQuadratureErrorsEnclosed = λ _ →
      everyRegularQuadratureRemainderEnclosed evaluator
  ; sumLowerContributionsExact = lowerContributionSumExact evaluator
  ; sumUpperContributionsExact = upperContributionSumExact evaluator
  ; regularRemainderInsideCertifiedInterval =
      regularRemainderInsideCertifiedInterval evaluator
  }

brillouinGridGenerationLevel : ProofLevel
brillouinGridGenerationLevel = machineChecked

brillouinGridCountLevel : ProofLevel
brillouinGridCountLevel = machineChecked

literalBoxEvaluationInputsLevel : ProofLevel
literalBoxEvaluationInputsLevel = conditional
