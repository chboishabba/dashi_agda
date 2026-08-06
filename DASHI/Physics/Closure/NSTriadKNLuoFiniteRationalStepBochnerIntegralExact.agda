module DASHI.Physics.Closure.NSTriadKNLuoFiniteRationalStepBochnerIntegralExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Tuomas Hytönen; Jan van Neerven; Mark Veraar; Lutz Weis.
-- Title: "Analysis in Banach Spaces, Volume I: Martingales and Littlewood--
-- Paley Theory".
-- Springer, 2016.
-- DOI: 10.1007/978-3-319-48520-1.
--
-- PURPOSE
-- Construct a concrete real-time simple-function layer rather than leave
-- "Bochner/Lebesgue integration" as an undifferentiated interface.  A finite
-- rational step function is a list of cells carrying an interval width and a
-- rational three-vector value.  Its integral is the exact weighted vector sum
--
--   sum_i width_i value_i.
--
-- The module proves concatenation additivity and invariance under subdividing
-- a time cell into two cells with the same value.  These are the algebraic
-- refinement laws needed before completing step functions in an L1 norm.
-- Countable completion, almost-everywhere quotienting and dominated
-- convergence remain separate constructive-analysis producers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; here; there)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V

record VectorStepCell : Set where
  constructor vector-step-cell
  field
    width : ℚ
    value : V.Vector3
    widthNonnegative : 0ℚ ≤ width

open VectorStepCell public

zeroVector : V.Vector3
zeroVector = V.v3 0ℚ 0ℚ 0ℚ

stepIntegral : List VectorStepCell → V.Vector3
stepIntegral [] = zeroVector
stepIntegral (cell ∷ cells) =
  V.add
    (V.scale (width cell) (value cell))
    (stepIntegral cells)

totalDuration : List VectorStepCell → ℚ
totalDuration [] = 0ℚ
totalDuration (cell ∷ cells) =
  width cell + totalDuration cells

appendCells :
  List VectorStepCell → List VectorStepCell → List VectorStepCell
appendCells [] right = right
appendCells (cell ∷ cells) right =
  cell ∷ appendCells cells right

stepIntegralAppend :
  (left right : List VectorStepCell) →
  stepIntegral (appendCells left right)
  ≡ V.add (stepIntegral left) (stepIntegral right)
stepIntegralAppend [] right =
  V.vectorExt
    (solve (V.x (stepIntegral right) ∷ []))
    (solve (V.y (stepIntegral right) ∷ []))
    (solve (V.z (stepIntegral right) ∷ []))
stepIntegralAppend (vector-step-cell cellWidth (V.v3 vx vy vz) widthNonnegative ∷ cells) right
  rewrite stepIntegralAppend cells right =
  V.vectorExt
    (solve
      ( cellWidth
      ∷ vx
      ∷ V.x (stepIntegral cells)
      ∷ V.x (stepIntegral right)
      ∷ []
      ))
    (solve
      ( cellWidth
      ∷ vy
      ∷ V.y (stepIntegral cells)
      ∷ V.y (stepIntegral right)
      ∷ []
      ))
    (solve
      ( cellWidth
      ∷ vz
      ∷ V.z (stepIntegral cells)
      ∷ V.z (stepIntegral right)
      ∷ []
      ))

totalDurationAppend :
  (left right : List VectorStepCell) →
  totalDuration (appendCells left right)
  ≡ totalDuration left + totalDuration right
totalDurationAppend [] right = solve (totalDuration right ∷ [])
totalDurationAppend (cell ∷ cells) right
  rewrite totalDurationAppend cells right =
  solve
    ( width cell
    ∷ totalDuration cells
    ∷ totalDuration right
    ∷ []
    )

splitCellIntegralInvariant :
  (whole leftWidth rightWidth : ℚ) →
  (cellValue : V.Vector3) →
  (wholeNonnegative : 0ℚ ≤ whole) →
  (leftNonnegative : 0ℚ ≤ leftWidth) →
  (rightNonnegative : 0ℚ ≤ rightWidth) →
  whole ≡ leftWidth + rightWidth →
  (remaining : List VectorStepCell) →
  stepIntegral
    (vector-step-cell whole cellValue wholeNonnegative ∷ remaining)
  ≡ stepIntegral
    ( vector-step-cell leftWidth cellValue leftNonnegative
    ∷ vector-step-cell rightWidth cellValue rightNonnegative
    ∷ remaining)
splitCellIntegralInvariant
  whole leftWidth rightWidth
  (V.v3 vx vy vz)
  wholeNonnegative leftNonnegative rightNonnegative
  widthSplit remaining =
  V.vectorExt
    (trans
      (cong
        (λ selectedWidth →
          selectedWidth * vx + V.x (stepIntegral remaining))
        widthSplit)
      (solve
        ( leftWidth
        ∷ rightWidth
        ∷ vx
        ∷ V.x (stepIntegral remaining)
        ∷ []
        )))
    (trans
      (cong
        (λ selectedWidth →
          selectedWidth * vy + V.y (stepIntegral remaining))
        widthSplit)
      (solve
        ( leftWidth
        ∷ rightWidth
        ∷ vy
        ∷ V.y (stepIntegral remaining)
        ∷ []
        )))
    (trans
      (cong
        (λ selectedWidth →
          selectedWidth * vz + V.z (stepIntegral remaining))
        widthSplit)
      (solve
        ( leftWidth
        ∷ rightWidth
        ∷ vz
        ∷ V.z (stepIntegral remaining)
        ∷ []
        )))

constantStepIntegral :
  (cells : List VectorStepCell) →
  (constant : V.Vector3) →
  ((cell : VectorStepCell) → cell ∈ cells → value cell ≡ constant) →
  stepIntegral cells ≡ V.scale (totalDuration cells) constant
constantStepIntegral [] (V.v3 cx cy cz) pointwise =
  V.vectorExt (solve (cx ∷ [])) (solve (cy ∷ [])) (solve (cz ∷ []))
constantStepIntegral (cell ∷ cells) constant pointwise
  rewrite pointwise cell (here refl)
        | constantStepIntegral
            cells
            constant
            (λ tailCell membership →
              pointwise tailCell (there membership)) =
  let
    constantCoordinates = constant
  in
  V.vectorExt
    (solve
      ( width cell
      ∷ V.x constantCoordinates
      ∷ totalDuration cells
      ∷ []
      ))
    (solve
      ( width cell
      ∷ V.y constantCoordinates
      ∷ totalDuration cells
      ∷ []
      ))
    (solve
      ( width cell
      ∷ V.z constantCoordinates
      ∷ totalDuration cells
      ∷ []
      ))
