module DASHI.Analysis.RiemannAristotleG2eDeterminantTaperKernelExact where

------------------------------------------------------------------------
-- G2e / DETERMINANT-TAPER KERNEL COMPRESSION
--
-- Once G2c identifies the one-dimensional Schur quotient with det3/W, the
-- literal reflection-paired response can be scalarized before summing zeros.
--
-- For fixed nuisance rows n1,n2 and a three-taper point-vector h(u), define
--
--   q(u) = det3(n1,n2,h(u)).
--
-- A reflection-paired zero sigma contributes a common scalar kernel
--
--   c_sigma(u) = 4 m_sigma cosh(a_sigma u) cos((b_sigma-t)u)
--
-- to every taper coordinate. Third-slot determinant linearity therefore gives
--
--   det3(n1,n2,c_sigma(u) * h(u)) = c_sigma(u) * q(u).
--
-- After integral linearity, the exact scalar zero response is
--
--   d_sigma = m_sigma ∫ 4 q(u) cosh(a_sigma u) cos((b_sigma-t)u) du.
--
-- Hence the entire G2e problem is a scalar compactly-supported cosine transform
-- of the local zero ordinates. No vector Gram or Schur geometry remains.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record DeterminantTaperAlgebra : Set₁ where
  constructor determinant-taper-algebra
  field
    Scalar Cell : Set
    multiply : Scalar → Scalar → Scalar
    scaleCell : Scalar → Cell → Cell
    determinantResponse : Cell → Scalar
    determinantScale : ∀ c x →
      determinantResponse (scaleCell c x)
      ≡ multiply c (determinantResponse x)

open DeterminantTaperAlgebra public

commonKernelMovesThroughDeterminant :
  (A : DeterminantTaperAlgebra) →
  (kernel : Scalar A) →
  (taperPoint : Cell A) →
  determinantResponse A (scaleCell A kernel taperPoint)
  ≡ multiply A kernel (determinantResponse A taperPoint)
commonKernelMovesThroughDeterminant A kernel taperPoint =
  determinantScale A kernel taperPoint

record G2eDeterminantTaperKernelBoundary : Set where
  constructor g2e-determinant-taper-kernel-boundary
  field
    thirdSlotDeterminantLinearityClosesPointwiseCompression : Bool
    thirdSlotDeterminantLinearityClosesPointwiseCompressionIsTrue :
      thirdSlotDeterminantLinearityClosesPointwiseCompression ≡ true

    literalReflectionKernelCommonAcrossThreeTaperCoordinates : Bool
    literalReflectionKernelCommonAcrossThreeTaperCoordinatesIsTrue :
      literalReflectionKernelCommonAcrossThreeTaperCoordinates ≡ true

    vectorGramGeometryRemainingAfterCompression : Bool
    vectorGramGeometryRemainingAfterCompressionIsFalse :
      vectorGramGeometryRemainingAfterCompression ≡ false

    exactScalarResponseFormula : String
    exactFiniteSumFormula : String

    targetCenteredLocalZeroExponentialSumBoundClosed : Bool
    targetCenteredLocalZeroExponentialSumBoundClosedIsFalse :
      targetCenteredLocalZeroExponentialSumBoundClosed ≡ false

canonicalG2eDeterminantTaperKernelBoundary : G2eDeterminantTaperKernelBoundary
canonicalG2eDeterminantTaperKernelBoundary =
  g2e-determinant-taper-kernel-boundary
    true refl
    true refl
    false refl
    "d_sigma = m_sigma * integral_u [4 q(u) cosh(a_sigma u) cos((b_sigma-t)u)], q(u)=det3(n1,n2,(projTaper(g_j,r)(u))_j)"
    "sum_sigma d_sigma = integral_u [4 q(u) * sum_sigma m_sigma cosh(a_sigma u) cos((b_sigma-t)u)]"
    false refl
