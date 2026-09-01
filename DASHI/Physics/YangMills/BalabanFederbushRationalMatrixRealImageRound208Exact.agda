{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact where

------------------------------------------------------------------------
-- ROUND208 BIDI: EXACT MATRIX-ACTION TRANSPORT ON THE RATIONAL IMAGE.
--
-- R207 embeds physical rational Lie3 coordinates into the literal real SU(2)
-- Lie carrier.  To transport the physical Federbush Jacobian action one needs
-- exactly one additional foundational law: multiplication is preserved by the
-- rational->real embedding.
--
-- With that law, finite 3x3 matrix action commutes exactly with embedding on
-- every rational input vector.  This is the strongest conclusion available
-- without silently promoting equality on the rational image to equality on all
-- real SU(2) Lie inputs.
--
-- The latter promotion requires an actual extension theorem (for example,
-- density of the rational image plus continuity of both operators) or a direct
-- theorem that the physical first derivative is already defined on the literal
-- real carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _+ℝ_; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanFiniteMatrixL1ContractionExact as L1
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Embed
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanFederbushRationalLieToRealSU2CarrierRound207Exact as R207

record RationalRealRingEmbedding : Set₁ where
  field
    additive : Embed.OrderedAdditiveRationalRealEmbedding
    multiplyExact : ∀ a b →
      Embed.embed (Embed.base additive) (a * b)
      ≡ Embed.embed (Embed.base additive) a
          *ℝ Embed.embed (Embed.base additive) b

open RationalRealRingEmbedding public

realSum : ∀ {A : Set} → List A → (A → ℝ) → ℝ
realSum [] value = 0ℝ
realSum (x ∷ xs) value = value x +ℝ realSum xs value

realSumCong :
  ∀ {A : Set} (values : List A) {left right : A → ℝ} →
  (∀ x → left x ≡ right x) →
  realSum values left ≡ realSum values right
realSumCong [] pointwise = refl
realSumCong (x ∷ xs) {left} {right} pointwise =
  trans
    (cong (left x +ℝ_) (realSumCong xs pointwise))
    (cong (_+ℝ realSum xs right) (pointwise x))

embedRationalSumExact :
  ∀ {A : Set}
    (embedding : RationalRealRingEmbedding)
    (values : List A) (value : A → ℚ) →
  Embed.embed (Embed.base (additive embedding))
    (Sums.sumRational values value)
  ≡ realSum values
      (λ x → Embed.embed (Embed.base (additive embedding)) (value x))
embedRationalSumExact embedding [] value =
  Embed.zeroExact (Embed.base (additive embedding))
embedRationalSumExact embedding (x ∷ xs) value =
  trans
    (Embed.addExact (additive embedding)
      (value x) (Sums.sumRational xs value))
    (cong
      (Embed.embed (Embed.base (additive embedding)) (value x) +ℝ_)
      (embedRationalSumExact embedding xs value))

realApplyMatrix :
  RationalRealRingEmbedding →
  Jacobian.Lie3Matrix → Jacobian.Lie3Vector →
  Physical.LieCoordinate3 → ℝ
realApplyMatrix embedding matrix vector row =
  realSum Physical.lieCoordinates3
    (λ column →
      Embed.embed (Embed.base (additive embedding)) (matrix row column)
      *ℝ Embed.embed (Embed.base (additive embedding)) (vector column))

rationalMatrixActionEmbeddingExact :
  ∀ embedding matrix vector row →
  Embed.embed (Embed.base (additive embedding))
    (L1.applyKernel Physical.lieCoordinates3 matrix vector row)
  ≡ realApplyMatrix embedding matrix vector row
rationalMatrixActionEmbeddingExact embedding matrix vector row =
  trans
    (embedRationalSumExact embedding Physical.lieCoordinates3
      (λ column → matrix row column * vector column))
    (realSumCong Physical.lieCoordinates3
      (λ column → multiplyExact embedding
        (matrix row column) (vector column)))

embeddedMatrixOutput :
  RationalRealRingEmbedding →
  Jacobian.Lie3Matrix → Jacobian.Lie3Vector →
  Lie.SU2LieAlgebra
embeddedMatrixOutput embedding matrix vector =
  R207.embedRationalLie3 (additive embedding)
    (L1.applyKernel Physical.lieCoordinates3 matrix vector)

embeddedMatrixOutputCoordinateExact :
  ∀ embedding matrix vector coordinate →
  R207.realLieCoordinate coordinate
    (embeddedMatrixOutput embedding matrix vector)
  ≡ realApplyMatrix embedding matrix vector coordinate
embeddedMatrixOutputCoordinateExact embedding matrix vector coordinate =
  trans
    (R207.embedRationalLie3CoordinateExact
      (additive embedding)
      (L1.applyKernel Physical.lieCoordinates3 matrix vector)
      coordinate)
    (rationalMatrixActionEmbeddingExact embedding matrix vector coordinate)

federbushRationalMatrixRealImageRound208Level : ProofLevel
federbushRationalMatrixRealImageRound208Level = machineChecked

rationalRealMultiplicativeEmbeddingRound208Level : ProofLevel
rationalRealMultiplicativeEmbeddingRound208Level = standardImported

-- Exact remaining promotion wall: equality on the embedded rational image is
-- not equality of operators on the complete real SU(2) carrier.  Supply either
-- a direct real-carrier derivative theorem or a valid extension principle such
-- as continuity plus density before identifying the operator with qSource.
literalFederbushRationalImageToFullRealQSourceRound208Level : ProofLevel
literalFederbushRationalImageToFullRealQSourceRound208Level = conditional
