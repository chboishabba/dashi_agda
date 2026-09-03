{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFederbushCanonicalRealMatrixExtensionRound210Exact where

------------------------------------------------------------------------
-- ROUND210 BIDI: CANONICAL REAL-SCALAR EXTENSION OF THE PHYSICAL RATIONAL
-- FEDERBUSH 3x3 OPERATOR.
--
-- R208 proves exact commutation on the rational image once multiplication is
-- preserved by the rational->real embedding.  No density theorem is actually
-- needed to obtain an operator on all real SU(2) Lie vectors: embed the nine
-- rational matrix coefficients and let that matrix act on the three literal
-- real coordinates.
--
-- This owner defines that everywhere-real extension and proves that it agrees
-- with the embedded rational output on every rational input.  The surviving
-- physical qSource seam is therefore only the pointwise identification of this
-- canonical real extension with the one-step Q(V0) operator used by Eq.(119).
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Embed
import DASHI.Physics.YangMills.BalabanFederbushRationalLieToRealSU2CarrierRound207Exact as R207
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208

realMatrixAction :
  R208.RationalRealRingEmbedding →
  Jacobian.Lie3Matrix → Lie.SU2LieAlgebra →
  Physical.LieCoordinate3 → ℝ
realMatrixAction embedding matrix vector row =
  R208.realSum Physical.lieCoordinates3
    (λ column →
      Embed.embed (Embed.base (R208.additive embedding)) (matrix row column)
      *ℝ R207.realLieCoordinate column vector)

canonicalRealMatrixExtension :
  R208.RationalRealRingEmbedding →
  Jacobian.Lie3Matrix →
  Lie.SU2LieAlgebra → Lie.SU2LieAlgebra
canonicalRealMatrixExtension embedding matrix vector =
  Lie.su2Lie
    (realMatrixAction embedding matrix vector Physical.coordinateX)
    (realMatrixAction embedding matrix vector Physical.coordinateY)
    (realMatrixAction embedding matrix vector Physical.coordinateZ)

canonicalRealMatrixExtensionCoordinateExact :
  ∀ embedding matrix vector coordinate →
  R207.realLieCoordinate coordinate
    (canonicalRealMatrixExtension embedding matrix vector)
  ≡ realMatrixAction embedding matrix vector coordinate
canonicalRealMatrixExtensionCoordinateExact embedding matrix vector Physical.coordinateX = refl
canonicalRealMatrixExtensionCoordinateExact embedding matrix vector Physical.coordinateY = refl
canonicalRealMatrixExtensionCoordinateExact embedding matrix vector Physical.coordinateZ = refl

realMatrixActionOnEmbeddedRationalExact :
  ∀ embedding matrix vector row →
  realMatrixAction embedding matrix
    (R207.embedRationalLie3 (R208.additive embedding) vector) row
  ≡ R208.realApplyMatrix embedding matrix vector row
realMatrixActionOnEmbeddedRationalExact embedding matrix vector row =
  R208.realSumCong Physical.lieCoordinates3
    (λ column →
      cong
        (Embed.embed (Embed.base (R208.additive embedding))
          (matrix row column) *ℝ_)
        (R207.embedRationalLie3CoordinateExact
          (R208.additive embedding) vector column))

canonicalRealExtensionAgreesOnRationalImage :
  ∀ embedding matrix vector →
  canonicalRealMatrixExtension embedding matrix
    (R207.embedRationalLie3 (R208.additive embedding) vector)
  ≡ R208.embeddedMatrixOutput embedding matrix vector
canonicalRealExtensionAgreesOnRationalImage embedding matrix vector =
  Lie.su2LieExt
    (coordinate Physical.coordinateX)
    (coordinate Physical.coordinateY)
    (coordinate Physical.coordinateZ)
  where
    coordinate : ∀ row →
      R207.realLieCoordinate row
        (canonicalRealMatrixExtension embedding matrix
          (R207.embedRationalLie3 (R208.additive embedding) vector))
      ≡ R207.realLieCoordinate row
          (R208.embeddedMatrixOutput embedding matrix vector)
    coordinate row =
      trans
        (canonicalRealMatrixExtensionCoordinateExact embedding matrix
          (R207.embedRationalLie3 (R208.additive embedding) vector) row)
        (trans
          (realMatrixActionOnEmbeddedRationalExact embedding matrix vector row)
          (sym
            (R208.embeddedMatrixOutputCoordinateExact
              embedding matrix vector row)))

federbushCanonicalRealMatrixExtensionRound210Level : ProofLevel
federbushCanonicalRealMatrixExtensionRound210Level = machineChecked

federbushRealExtensionRationalImageCompatibilityRound210Level : ProofLevel
federbushRealExtensionRationalImageCompatibilityRound210Level = machineChecked

-- The multiplication-preserving scalar embedding required by R208/R210 is
-- still a physical/foundational inhabitant, not manufactured here.
literalRationalRealRingEmbeddingRound210Level : ProofLevel
literalRationalRealRingEmbeddingRound210Level = conditional

-- Final source-facing same-object seam after representation and extension are
-- generated: the actual one-step Q(V0) operator must equal this canonical real
-- extension of the independently produced physical Federbush first derivative.
literalFederbushRealExtensionIsEquation119QSourceRound210Level : ProofLevel
literalFederbushRealExtensionIsEquation119QSourceRound210Level = conditional
