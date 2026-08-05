module DASHI.Physics.YangMills.BalabanP33BishopChordMetricSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Grundlehren der mathematischen Wissenschaften 279,
-- Springer, 1985. DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Close identity of indiscernibles for the square-root chord construction.
-- The proof is constructive and setoid-valued:
--
--   d_ch(q,r) = 0  ==>  q approximately-equals r componentwise.
--
-- It proceeds through four exact steps:
--
--   1. sqrt(x)=0 and x>=0 imply x=0 by squaring;
--   2. ||q-r||^2=0 forces every coordinate square to be zero because each
--      square is nonnegative and bounded above by the full four-square sum;
--   3. x^2=0 implies |x|=0 through sqrt(x^2)=|x|;
--   4. |x|=0 implies x=0 from -|x|<=x<=|x|.
--
-- Together with the symmetry, reflexivity and triangle theorem in
-- BalabanP33BishopR4ChordMetricFromSquareRootExact, this completes the metric
-- laws once the scalar Bishop square-root backend is constructed.
------------------------------------------------------------------------

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanClayT2BishopQuaternionNormalizationExact as Quaternion
import DASHI.Physics.YangMills.BalabanP33BishopLiteralQuaternionExponentialChordExact as Literal
import DASHI.Physics.YangMills.BalabanP33BishopR4ChordMetricFromSquareRootExact as Metric
open import DASHI.Physics.YangMills.CompactLieProofLevel

square : BishopReal.ℝ → BishopReal.ℝ
square = Metric.square

zeroSquare :
  BishopReal._≃_ (square BishopReal.0ℝ) BishopReal.0ℝ
zeroSquare =
  let open BishopProperties.ℝ-Solver
  in solve 0
    ((Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1)) ⊜ Κ (+ 0 / 1))
    BishopProperties.≃-refl

rootZero :
  (roots : Metric.BishopSquareRootCalculus) →
  BishopReal._≃_ (Metric.root roots BishopReal.0ℝ) BishopReal.0ℝ
rootZero roots =
  BishopProperties.≃-trans
    (Metric.rootCongruent roots (BishopProperties.≃-symm zeroSquare))
    (BishopProperties.≃-trans
      (Metric.rootOfSquare roots BishopReal.0ℝ)
      (BishopProperties.nonNegx⇒∣x∣≃x BishopProperties.nonNeg0))

rootZeroReflectsInput :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ value →
  BishopReal.NonNegative value →
  BishopReal._≃_ (Metric.root roots value) BishopReal.0ℝ →
  BishopReal._≃_ value BishopReal.0ℝ
rootZeroReflectsInput roots value valueNonnegative rootValueZero =
  BishopProperties.≃-trans
    (BishopProperties.≃-symm
      (Metric.rootSquare roots value valueNonnegative))
    (BishopProperties.≃-trans
      (BishopProperties.*-cong rootValueZero rootValueZero)
      zeroSquare)

absoluteZeroImpliesZero : ∀ value →
  BishopReal._≃_ (BishopReal.∣ value ∣) BishopReal.0ℝ →
  BishopReal._≃_ value BishopReal.0ℝ
absoluteZeroImpliesZero value absoluteZero =
  let
    valueBelowZero : BishopReal._≤_ value BishopReal.0ℝ
    valueBelowZero =
      BishopProperties.≤-respʳ-≃ absoluteZero
        BishopProperties.x≤∣x∣

    negativeBelowZero : BishopReal._≤_ (BishopReal.- value) BishopReal.0ℝ
    negativeBelowZero =
      BishopProperties.≤-respʳ-≃
        (BishopProperties.≃-trans
          BishopProperties.∣-x∣≃∣x∣ absoluteZero)
        BishopProperties.x≤∣x∣

    zeroBelowValue : BishopReal._≤_ BishopReal.0ℝ value
    zeroBelowValue =
      BishopProperties.≤-respʳ-≃
        (let open BishopProperties.ℝ-Solver
         in solve 1
           (λ x → - (- x) ⊜ x)
           BishopProperties.≃-refl value)
        (BishopProperties.≤-respˡ-≃
          (let open BishopProperties.ℝ-Solver
           in solve 0
             ((- Κ (+ 0 / 1)) ⊜ Κ (+ 0 / 1))
             BishopProperties.≃-refl)
          (BishopProperties.neg-mono-≤ negativeBelowZero))
  in
  BishopProperties.≤-antisym valueBelowZero zeroBelowValue

squareZeroImpliesZero :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ value →
  BishopReal._≃_ (square value) BishopReal.0ℝ →
  BishopReal._≃_ value BishopReal.0ℝ
squareZeroImpliesZero roots value squareZeroProof =
  let
    absoluteZero :
      BishopReal._≃_ (BishopReal.∣ value ∣) BishopReal.0ℝ
    absoluteZero =
      BishopProperties.≃-trans
        (BishopProperties.≃-symm (Metric.rootOfSquare roots value))
        (BishopProperties.≃-trans
          (Metric.rootCongruent roots squareZeroProof)
          (rootZero roots))
  in absoluteZeroImpliesZero value absoluteZero

------------------------------------------------------------------------
-- Each coordinate square lies below the full four-square sum.
------------------------------------------------------------------------

component0BelowNormSq :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ a0 a1 a2 a3 →
  BishopReal._≤_ (square a0)
    (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
component0BelowNormSq roots a0 a1 a2 a3 =
  let
    restNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx+y
        (Metric.squareNonnegative roots a1)
        (BishopProperties.nonNegx,y⇒nonNegx+y
          (Metric.squareNonnegative roots a2)
          (Metric.squareNonnegative roots a3))
  in
  BishopProperties.≤-respˡ-≃
    (BishopProperties.≃-symm
      (BishopProperties.+-identityʳ (square a0)))
    (BishopProperties.+-monoʳ-≤ (square a0)
      (BishopProperties.nonNegx⇒0≤x restNonnegative))

component1BelowNormSq :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ a0 a1 a2 a3 →
  BishopReal._≤_ (square a1)
    (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
component1BelowNormSq roots a0 a1 a2 a3 =
  let
    others = BishopReal._+_ (square a0)
      (BishopReal._+_ (square a2) (square a3))
    othersNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx+y
        (Metric.squareNonnegative roots a0)
        (BishopProperties.nonNegx,y⇒nonNegx+y
          (Metric.squareNonnegative roots a2)
          (Metric.squareNonnegative roots a3))
    gapIdentity :
      BishopReal._≃_
        (BishopReal._-_
          (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
          (square a1))
        others
    gapIdentity =
      let open BishopProperties.ℝ-Solver
      in solve 4
        (λ a0 a1 a2 a3 →
          ((a0 ⊗ a0
            ⊕ (a1 ⊗ a1 ⊕ (a2 ⊗ a2 ⊕ a3 ⊗ a3)))
            ⊖ a1 ⊗ a1)
          ⊜ a0 ⊗ a0 ⊕ (a2 ⊗ a2 ⊕ a3 ⊗ a3))
        BishopProperties.≃-refl a0 a1 a2 a3
  in
  BishopProperties.0≤y-x⇒x≤y
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm gapIdentity)
      (BishopProperties.nonNegx⇒0≤x othersNonnegative))

component2BelowNormSq :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ a0 a1 a2 a3 →
  BishopReal._≤_ (square a2)
    (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
component2BelowNormSq roots a0 a1 a2 a3 =
  let
    others = BishopReal._+_ (square a0)
      (BishopReal._+_ (square a1) (square a3))
    othersNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx+y
        (Metric.squareNonnegative roots a0)
        (BishopProperties.nonNegx,y⇒nonNegx+y
          (Metric.squareNonnegative roots a1)
          (Metric.squareNonnegative roots a3))
    gapIdentity :
      BishopReal._≃_
        (BishopReal._-_
          (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
          (square a2))
        others
    gapIdentity =
      let open BishopProperties.ℝ-Solver
      in solve 4
        (λ a0 a1 a2 a3 →
          ((a0 ⊗ a0
            ⊕ (a1 ⊗ a1 ⊕ (a2 ⊗ a2 ⊕ a3 ⊗ a3)))
            ⊖ a2 ⊗ a2)
          ⊜ a0 ⊗ a0 ⊕ (a1 ⊗ a1 ⊕ a3 ⊗ a3))
        BishopProperties.≃-refl a0 a1 a2 a3
  in
  BishopProperties.0≤y-x⇒x≤y
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm gapIdentity)
      (BishopProperties.nonNegx⇒0≤x othersNonnegative))

component3BelowNormSq :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ a0 a1 a2 a3 →
  BishopReal._≤_ (square a3)
    (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
component3BelowNormSq roots a0 a1 a2 a3 =
  let
    others = BishopReal._+_ (square a0)
      (BishopReal._+_ (square a1) (square a2))
    othersNonnegative =
      BishopProperties.nonNegx,y⇒nonNegx+y
        (Metric.squareNonnegative roots a0)
        (BishopProperties.nonNegx,y⇒nonNegx+y
          (Metric.squareNonnegative roots a1)
          (Metric.squareNonnegative roots a2))
    gapIdentity :
      BishopReal._≃_
        (BishopReal._-_
          (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3))
          (square a3))
        others
    gapIdentity =
      let open BishopProperties.ℝ-Solver
      in solve 4
        (λ a0 a1 a2 a3 →
          ((a0 ⊗ a0
            ⊕ (a1 ⊗ a1 ⊕ (a2 ⊗ a2 ⊕ a3 ⊗ a3)))
            ⊖ a3 ⊗ a3)
          ⊜ a0 ⊗ a0 ⊕ (a1 ⊗ a1 ⊕ a2 ⊗ a2))
        BishopProperties.≃-refl a0 a1 a2 a3
  in
  BishopProperties.0≤y-x⇒x≤y
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm gapIdentity)
      (BishopProperties.nonNegx⇒0≤x othersNonnegative))

componentSquareZero :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ component norm →
  BishopReal.NonNegative (square component) →
  BishopReal._≤_ (square component) norm →
  BishopReal._≃_ norm BishopReal.0ℝ →
  BishopReal._≃_ (square component) BishopReal.0ℝ
componentSquareZero roots component norm componentNonnegative componentBelow normZero =
  BishopProperties.≤-antisym
    (BishopProperties.≤-respʳ-≃ normZero componentBelow)
    (BishopProperties.nonNegx⇒0≤x componentNonnegative)

record Vec4Equivalent (left right : Metric.Vec4B) : Set where
  field
    coordinate0 : BishopReal._≃_ (Metric.x0 left) (Metric.x0 right)
    coordinate1 : BishopReal._≃_ (Metric.x1 left) (Metric.x1 right)
    coordinate2 : BishopReal._≃_ (Metric.x2 left) (Metric.x2 right)
    coordinate3 : BishopReal._≃_ (Metric.x3 left) (Metric.x3 right)

open Vec4Equivalent public

normZeroImpliesVec4Zero :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ a0 a1 a2 a3 →
  BishopReal._≃_
    (Metric.root roots
      (Metric.normSq4 (Metric.vec4B a0 a1 a2 a3)))
    BishopReal.0ℝ →
  Vec4Equivalent
    (Metric.vec4B a0 a1 a2 a3)
    (Metric.vec4B BishopReal.0ℝ BishopReal.0ℝ BishopReal.0ℝ BishopReal.0ℝ)
normZeroImpliesVec4Zero roots a0 a1 a2 a3 normZero =
  let
    vector = Metric.vec4B a0 a1 a2 a3
    normSquaredZero = rootZeroReflectsInput roots
      (Metric.normSq4 vector)
      (Metric.normSq4Nonnegative roots vector)
      normZero

    zero0 = componentSquareZero roots a0 (Metric.normSq4 vector)
      (Metric.squareNonnegative roots a0)
      (component0BelowNormSq roots a0 a1 a2 a3) normSquaredZero
    zero1 = componentSquareZero roots a1 (Metric.normSq4 vector)
      (Metric.squareNonnegative roots a1)
      (component1BelowNormSq roots a0 a1 a2 a3) normSquaredZero
    zero2 = componentSquareZero roots a2 (Metric.normSq4 vector)
      (Metric.squareNonnegative roots a2)
      (component2BelowNormSq roots a0 a1 a2 a3) normSquaredZero
    zero3 = componentSquareZero roots a3 (Metric.normSq4 vector)
      (Metric.squareNonnegative roots a3)
      (component3BelowNormSq roots a0 a1 a2 a3) normSquaredZero
  in record
    { coordinate0 = squareZeroImpliesZero roots a0 zero0
    ; coordinate1 = squareZeroImpliesZero roots a1 zero1
    ; coordinate2 = squareZeroImpliesZero roots a2 zero2
    ; coordinate3 = squareZeroImpliesZero roots a3 zero3
    }

literalChordZeroImpliesQuaternionEquivalent :
  (roots : Metric.BishopSquareRootCalculus) →
  ∀ left right →
  BishopReal._≃_
    (Metric.literalChordDistance roots left right)
    BishopReal.0ℝ →
  Quaternion.QuaternionBEquivalent left right
literalChordZeroImpliesQuaternionEquivalent roots
    (Quaternion.quaternionB l0 (Quaternion.vec3B l1 l2 l3))
    (Quaternion.quaternionB r0 (Quaternion.vec3B r1 r2 r3)) chordZero =
  let
    difference = Metric.vec4B
      (BishopReal._-_ l0 r0) (BishopReal._-_ l1 r1)
      (BishopReal._-_ l2 r2) (BishopReal._-_ l3 r3)
    differenceZero = normZeroImpliesVec4Zero roots
      (BishopReal._-_ l0 r0) (BishopReal._-_ l1 r1)
      (BishopReal._-_ l2 r2) (BishopReal._-_ l3 r3)
      (BishopProperties.≃-trans
        (Metric.rootCongruent roots
          (BishopProperties.≃-symm
            (Metric.literalChordSqAsNormSq
              (Quaternion.quaternionB l0 (Quaternion.vec3B l1 l2 l3))
              (Quaternion.quaternionB r0 (Quaternion.vec3B r1 r2 r3)))))
        chordZero)

    differenceZeroToEquality : ∀ leftCoordinate rightCoordinate →
      BishopReal._≃_
        (BishopReal._-_ leftCoordinate rightCoordinate)
        BishopReal.0ℝ →
      BishopReal._≃_ leftCoordinate rightCoordinate
    differenceZeroToEquality leftCoordinate rightCoordinate differenceIsZero =
      BishopProperties.≃-trans
        (BishopProperties.≃-symm
          (BishopProperties.+-identityʳ leftCoordinate))
        (BishopProperties.≃-trans
          (BishopProperties.+-cong BishopProperties.≃-refl
            (BishopProperties.≃-symm differenceIsZero))
          (let open BishopProperties.ℝ-Solver
           in solve 2
             (λ left right →
               left ⊕ (left ⊖ right) ⊜ right)
             BishopProperties.≃-refl leftCoordinate rightCoordinate))
  in record
    { Quaternion.QuaternionBEquivalent.scalarEquivalent =
        differenceZeroToEquality l0 r0 (coordinate0 differenceZero)
    ; Quaternion.QuaternionBEquivalent.xEquivalent =
        differenceZeroToEquality l1 r1 (coordinate1 differenceZero)
    ; Quaternion.QuaternionBEquivalent.yEquivalent =
        differenceZeroToEquality l2 r2 (coordinate2 differenceZero)
    ; Quaternion.QuaternionBEquivalent.zEquivalent =
        differenceZeroToEquality l3 r3 (coordinate3 differenceZero)
    }

p33BishopRootZeroReflectionLevel : ProofLevel
p33BishopRootZeroReflectionLevel = machineChecked

p33BishopFourSquareSeparationLevel : ProofLevel
p33BishopFourSquareSeparationLevel = machineChecked

p33BishopChordIdentityOfIndiscerniblesLevel : ProofLevel
p33BishopChordIdentityOfIndiscerniblesLevel = machineChecked
