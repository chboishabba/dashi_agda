module DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact where

-- SOURCE-WRITTEN, UNCOMPILED. Mirror the literal raw rational expressions
-- in Integration/Paper9LiteralCross.lean, on the ORIGINAL Agda owners.
-- This is native coordinate correspondence, not imported Lean evidence.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _^_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Maybe using (just)
open import Data.Product.Base using (_×_; _,_; Σ; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
import Data.Nat.DivMod as ND
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyPairedTotalityExact as T
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as F
import DASHI.Foundations.BishopChudnovskyRationalOverlapExact as O
import DASHI.Foundations.BishopChudnovskySignedCrossReflectionExact as X
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as P
import DASHI.Analysis.BishopMachinRationalStageEmbeddingExact as S
import DASHI.Analysis.BishopMachinCrossEnvelopeBishopOrderExact as R
import DASHI.Foundations.BishopMachinArctanConstructionExact as M
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as I

-- The actual signed integer recurrence, retaining zero and negative terms.
sign : Nat → Z.ℤ
sign zero = Z.+ 1
sign (suc n) = Z._*_ (sign n) (Z.-_ (Z.+ 1))

signCorrect : (n : Nat) → S.qSign n ≡ Q.mkℚᵘ (sign n) 0
signCorrect zero = refl
signCorrect (suc n) rewrite signCorrect n = refl

omittedDen : (d n : Nat) → Nat
omittedDen d n = I.oddExponent n * (d ^ I.oddExponent n)

omittedNZ : (d n : Nat) → N.NonZero d → N.NonZero (omittedDen d n)
omittedNZ d n nz = F.prodNZ (I.oddExponent n) (d ^ I.oddExponent n)
  (M.oddExponentNonZero n) (NP.m^n≢0 d (I.oddExponent n) {{nz}})

-- Scale a fraction by an integer without relying on definitionally
-- identical denominator grouping. The original fracWeight owns this.
scaleFraction : (s t : Z.ℤ) (d : Nat) (nz : N.NonZero d) →
  (F.frac s 1 N.nonZero Q.* F.frac t d nz) Q.≃
  F.frac (Z._*_ s t) d nz
scaleFraction s t d nz =
  QP.≃-trans (QP.*-comm _ _)
    (QP.≃-trans (QP.≃-sym (F.fracWeight t s d nz))
      (QP.≃-reflexive (cong (λ v → F.frac v d nz) (ZP.*-comm t s))))

unsignedAtan : (d n : Nat) (nz : N.NonZero d) → Q.ℚᵘ
unsignedAtan d n nz = F.frac (Z.+ 1) (omittedDen d n) (omittedNZ d n nz)

unsignedCorrect : (d n : Nat) (nz : N.NonZero d) →
  (M.inverseOddRational n Q.* S.qPow (F.frac (Z.+ 1) d nz) (I.oddExponent n))
    Q.≃ unsignedAtan d n nz
unsignedCorrect d n nz =
  QP.≃-trans
    (QP.*-cong QP.≃-refl (R.rationalReciprocalPower d {{nz}} (I.oddExponent n)))
    (QP.≃-sym (F.fracMulEdge (Z.+ 1) (Z.+ 1)
      (I.oddExponent n) (d ^ I.oddExponent n)
      (M.oddExponentNonZero n) (NP.m^n≢0 d (I.oddExponent n) {{nz}})))

weighted : (c : Z.ℤ) (d n : Nat) (nz : N.NonZero d) → Q.ℚᵘ
weighted c d n nz = F.frac (Z._*_ c (sign n)) (omittedDen d n) (omittedNZ d n nz)

weightedCorrect : (c : Z.ℤ) (d n : Nat) (nz : N.NonZero d) →
  (F.frac c 1 N.nonZero Q.* S.qAtanTerm (F.frac (Z.+ 1) d nz) n)
    Q.≃ weighted c d n nz
weightedCorrect c d n nz rewrite signCorrect n =
  QP.≃-trans
    (QP.*-cong QP.≃-refl
      (QP.*-cong QP.≃-refl (unsignedCorrect d n nz)))
    (QP.≃-trans
      (QP.*-cong QP.≃-refl
        (scaleFraction (sign n) (Z.+ 1) (omittedDen d n) (omittedNZ d n nz)))
      (QP.≃-trans
        (scaleFraction c (Z._*_ (sign n) (Z.+ 1)) (omittedDen d n) (omittedNZ d n nz))
        (QP.≃-reflexive (cong
          (λ v → F.frac (Z._*_ c v) (omittedDen d n) (omittedNZ d n nz))
          (ZP.*-identityʳ (sign n))))))

rawTerm : Nat → Q.ℚᵘ
rawTerm n = weighted (Z.+ 16) 5 n N.nonZero Q.- weighted (Z.+ 4) 239 n N.nonZero

termCorrect : (n : Nat) → rawTerm n Q.≃ S.qMachinTerm n
termCorrect n = QP.≃-sym (QP.+-cong
  (weightedCorrect (Z.+ 16) 5 n N.nonZero)
  (QP.-‿cong (weightedCorrect (Z.+ 4) 239 n N.nonZero)))

-- Actual raw (ad+cb,bd) recurrence. The unnormalised rational owner
-- already implements this exact recurrence; no normalized Rat is used.
rawStage : Nat → Q.ℚᵘ
rawStage zero = Q.0ℚᵘ
rawStage (suc n) = rawStage n Q.+ rawTerm n

stageCorrect : (n : Nat) → rawStage n Q.≃ S.qMachinStage n
stageCorrect zero = QP.≃-refl
stageCorrect (suc n) = QP.+-cong (stageCorrect n) (termCorrect n)

stageNumStep : (n : Nat) →
  Q.↥ (rawStage (suc n)) ≡
  Z._+_ (Z._*_ (Q.↥ (rawStage n)) (Q.↧ (rawTerm n)))
        (Z._*_ (Q.↥ (rawTerm n)) (Q.↧ (rawStage n)))
stageNumStep n = X.sumNum (rawStage n) (rawTerm n)

stageDenStep : (n : Nat) →
  Q.↧ (rawStage (suc n)) ≡ Z._*_ (Q.↧ (rawStage n)) (Q.↧ (rawTerm n))
stageDenStep n = X.sumDen (rawStage n) (rawTerm n)

-- Literal zero mode and geometric radius.
rawRadius : Nat → Q.ℚᵘ
rawRadius zero = F.frac (Z.+ 22) 7 N.nonZero
rawRadius (suc n) = F.frac (Z.+ 4) (25 ^ suc n) (NP.m^n≢0 25 (suc n))

radiusCorrect : (n : Nat) → rawRadius n Q.≃ O.machinRadius n
radiusCorrect zero = QP.≃-refl
radiusCorrect (suc n) = QP.≃-refl

-- The literal Lean nonempty prefix has Q : Nat, T : Int; B=1.
-- Extract both from existing raw source. Absolute value of T is used
-- ONLY after the nonempty positivity proof, not on P or the cross.
rawT : Nat → Nat
rawT n = Z.∣ E.T (suc n) ∣

rawTCorrect : (n : Nat) (v : W.View n) → rawT n ≡ CH.num (W.value v)
rawTCorrect n v rewrite W.numEq v = refl

rawQCorrect : (n : Nat) (v : W.View n) → G.qProduct (suc n) ≡ CH.den (W.value v)
rawQCorrect n v = sym (W.sourceDen n v)

-- Build the independent source-shaped corners after explicit T,Q
-- projection. The positive views provide only witnesses, not values
-- of the cross inequalities.
rawView : (n : Nat) → CH.PositiveSum
rawView n with T.allNonemptyTPositive n | T.prefixQPositive (suc n)
... | T.pos t _ | T.pos q _ = CH.positiveSum t q

rawViewCorrect : (n : Nat) → rawView n ≡ W.value (W.sourceView n)
rawViewCorrect n with T.allNonemptyTPositive n | T.prefixQPositive (suc n)
... | T.pos t te | T.pos q qe rewrite te | qe | E.prefixBOne (suc n)
  | NP.*-identityʳ q | NP.+-identityʳ q = refl

rawWindow : Nat → CH.Interval
rawWindow k with T.successorWitness (CH.rootScale k) (NP.m^n≢0 2 (CH.rootBits k))
... | sp , _ = CH.orderedInterval sp (CH.rootNumerator k)
  (rawView ((k + 4) ND./ 41)) (rawView (CH.cutoff k))

windowCorrect : (k : Nat) → rawWindow k ≡ O.window k
windowCorrect k with T.successorWitness (CH.rootScale k) (NP.m^n≢0 2 (CH.rootBits k))
... | sp , se =
  let
    x = W.sourceView ((k + 4) ND./ 41)
    y = W.sourceView (CH.cutoff k)
    actual : CH.intervalAt k ≡ just (CH.orderedInterval sp (CH.rootNumerator k) (W.value x) (W.value y))
    actual rewrite se | W.computes x | W.computes y = refl
    same = W.justInjective (trans (sym actual) (O.computed k))
  in trans (cong (λ v → CH.orderedInterval sp (CH.rootNumerator k) v (rawView (CH.cutoff k)))
      (rawViewCorrect ((k + 4) ND./ 41)))
    (trans (cong (CH.orderedInterval sp (CH.rootNumerator k) (W.value x))
      (rawViewCorrect (CH.cutoff k))) same)

lowerCorrect : (k : Nat) → CH.lower (rawWindow k) Q.≃ CH.lower (O.window k)
lowerCorrect k = QP.≃-reflexive (cong CH.lower (windowCorrect k))

upperCorrect : (k : Nat) → CH.upper (rawWindow k) Q.≃ CH.upper (O.window k)
upperCorrect k = QP.≃-reflexive (cong CH.upper (windowCorrect k))

-- Concrete native raw endpoint, not an assumed theorem of Lean.
RawCross : Nat → Set
RawCross k =
  X.ExpandedLeAdd (CH.lower (rawWindow k)) (rawStage k) (rawRadius k)
  × X.ExpandedLeAdd (rawStage k) (CH.upper (rawWindow k)) (rawRadius k)

toExpanded : (k : Nat) → RawCross k → X.ExpandedCross k
toExpanded k = X.expandedCrossFromEquivalentCoordinates k
  (CH.lower (rawWindow k)) (CH.upper (rawWindow k)) (rawStage k) (rawRadius k)
  (lowerCorrect k) (upperCorrect k) (stageCorrect k) (radiusCorrect k)

fromExpanded : (k : Nat) → X.ExpandedCross k → RawCross k
fromExpanded k = X.expandedCrossToEquivalentCoordinates k
  (CH.lower (rawWindow k)) (CH.upper (rawWindow k)) (rawStage k) (rawRadius k)
  (lowerCorrect k) (upperCorrect k) (stageCorrect k) (radiusCorrect k)

periodFromRaw : ((k : Nat) → RawCross k) → P.NativePeriod
periodFromRaw h = P.expandedToPeriod (λ k → toExpanded k (h k))

rawFromPeriod : P.NativePeriod → (k : Nat) → RawCross k
rawFromPeriod h k = fromExpanded k (P.periodToExpanded h k)
