{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanFederbushRationalLieToRealSU2CarrierRound207Exact where

------------------------------------------------------------------------
-- ROUND207 BIDI: RATIONAL FEDERBUSH LIE3 COORDINATES -> LITERAL REAL SU(2)
-- LIE CARRIER.
--
-- The theorem-bearing physical equation-(0.11) derivative lane uses the finite
-- rational coordinate carrier
--
--   Lie3Vector = LieCoordinate3 -> Q,
--
-- whereas the strongest Eq.(119) producer uses the repository's literal
-- `SU2LieAlgebra`, whose three components live in the real-analysis carrier.
--
-- This module removes only that carrier mismatch, using the already-owned
-- rational->real embedding interface.  It does NOT identify the equation-(0.11)
-- derivative operator with R193/R178 `qSource`; that remaining statement is now
-- a pure operator same-object theorem rather than a representation ambiguity.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalSU2FiniteCoordinatesExact as Physical
import DASHI.Physics.YangMills.BalabanCMP109FederbushNormalizedJacobianExact as Jacobian
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as Embed

rationalCoordinate : Physical.LieCoordinate3 → Jacobian.Lie3Vector → ℚ
rationalCoordinate coordinate vector = vector coordinate

realLieCoordinate : Physical.LieCoordinate3 → Lie.SU2LieAlgebra → ℝ
realLieCoordinate Physical.coordinateX value = Lie.xComponent value
realLieCoordinate Physical.coordinateY value = Lie.yComponent value
realLieCoordinate Physical.coordinateZ value = Lie.zComponent value

embedRationalLie3 :
  Embed.OrderedAdditiveRationalRealEmbedding →
  Jacobian.Lie3Vector → Lie.SU2LieAlgebra
embedRationalLie3 embedding vector =
  Lie.su2Lie
    (Embed.embed (Embed.base embedding)
      (vector Physical.coordinateX))
    (Embed.embed (Embed.base embedding)
      (vector Physical.coordinateY))
    (Embed.embed (Embed.base embedding)
      (vector Physical.coordinateZ))

embedRationalLie3CoordinateExact :
  ∀ embedding vector coordinate →
  realLieCoordinate coordinate (embedRationalLie3 embedding vector)
  ≡ Embed.embed (Embed.base embedding) (vector coordinate)
embedRationalLie3CoordinateExact embedding vector Physical.coordinateX = refl
embedRationalLie3CoordinateExact embedding vector Physical.coordinateY = refl
embedRationalLie3CoordinateExact embedding vector Physical.coordinateZ = refl

embedRationalLie3ZeroExact :
  ∀ embedding →
  embedRationalLie3 embedding (λ _ → 0ℚ)
  ≡ Lie.lieZero
embedRationalLie3ZeroExact embedding =
  Lie.su2LieExt
    (Embed.zeroExact (Embed.base embedding))
    (Embed.zeroExact (Embed.base embedding))
    (Embed.zeroExact (Embed.base embedding))

-- Additivity is enough to show that finite coordinate sums transport to the
-- literal SU(2) additive carrier.  Matrix/operator compatibility additionally
-- needs the exact scalar-multiplication transport used by the physical
-- Federbush Jacobian action; that is intentionally left at the next seam.
embedRationalLie3AddExact :
  ∀ embedding left right →
  embedRationalLie3 embedding
    (λ coordinate → left coordinate + right coordinate)
  ≡ Lie.lieAdd
      (embedRationalLie3 embedding left)
      (embedRationalLie3 embedding right)
embedRationalLie3AddExact embedding left right =
  Lie.su2LieExt
    (Embed.addExact embedding
      (left Physical.coordinateX) (right Physical.coordinateX))
    (Embed.addExact embedding
      (left Physical.coordinateY) (right Physical.coordinateY))
    (Embed.addExact embedding
      (left Physical.coordinateZ) (right Physical.coordinateZ))

federbushRationalLieToRealSU2CarrierRound207Level : ProofLevel
federbushRationalLieToRealSU2CarrierRound207Level = machineChecked

federbushRationalLieCoordinateExactRound207Level : ProofLevel
federbushRationalLieCoordinateExactRound207Level = machineChecked

-- Exact surviving source theorem: after transporting the physical equation-(0.11)
-- first derivative to this real SU(2) carrier, identify that operator with the
-- independently sourced one-step Q(V0) field used as R193/R178 `qSource`.
literalFederbushFirstDerivativeIsEquation119QSourceRound207Level : ProofLevel
literalFederbushFirstDerivativeIsEquation119QSourceRound207Level = conditional
