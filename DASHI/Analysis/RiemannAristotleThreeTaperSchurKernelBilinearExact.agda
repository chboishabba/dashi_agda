module DASHI.Analysis.RiemannAristotleThreeTaperSchurKernelBilinearExact where

------------------------------------------------------------------------
-- G2 / EXACT THREE-TAPER SCHUR-KERNEL BILINEAR COMPILER
--
-- This is pure representation algebra.  It does not choose the literal Schur
-- coefficients and does not estimate any zeta sum.
--
-- A raw reflection-paired zero contribution has three taper coordinates
--
--   k = (k0,k1,k2).
--
-- A fixed deterministic Schur operator E on this response space is represented
-- by three rows.  The post-Schur covariance is definitionally
--
--   <E k_sigma, E k_tau>
--     = sum_r (sum_m E_rm k_m(sigma)) (sum_n E_rn k_n(tau)).
--
-- Thus once the literal Lean `elim2` response is welded to one fixed matrix E,
-- every Gram cross term is already expressed in the raw reflection-paired
-- kernel coordinates.  No E=identity shortcut is used.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

record ScalarBilinearSurface : Set₁ where
  constructor scalar-bilinear-surface
  field
    Scalar : Set
    zero : Scalar
    add multiply : Scalar → Scalar → Scalar

open ScalarBilinearSurface public

record Triple (S : ScalarBilinearSurface) : Set where
  constructor triple
  field
    c0 c1 c2 : Scalar S

open Triple public

record Row3 (S : ScalarBilinearSurface) : Set where
  constructor row3
  field
    a0 a1 a2 : Scalar S

open Row3 public

record Matrix3 (S : ScalarBilinearSurface) : Set where
  constructor matrix3
  field
    r0 r1 r2 : Row3 S

open Matrix3 public

rowApply :
  (S : ScalarBilinearSurface) →
  Row3 S → Triple S → Scalar S
rowApply S r x =
  add S
    (add S
      (multiply S (a0 r) (c0 x))
      (multiply S (a1 r) (c1 x)))
    (multiply S (a2 r) (c2 x))

schurApply :
  (S : ScalarBilinearSurface) →
  Matrix3 S → Triple S → Triple S
schurApply S E x =
  triple
    (rowApply S (r0 E) x)
    (rowApply S (r1 E) x)
    (rowApply S (r2 E) x)

dot3 :
  (S : ScalarBilinearSurface) →
  Triple S → Triple S → Scalar S
dot3 S x y =
  add S
    (add S
      (multiply S (c0 x) (c0 y))
      (multiply S (c1 x) (c1 y)))
    (multiply S (c2 x) (c2 y))

-- Literal covariance in raw kernel coordinates.  We deliberately retain the
-- row-linear forms rather than taking an absolute value or collapsing E.
schurKernelCovariance :
  (S : ScalarBilinearSurface) →
  Matrix3 S → Triple S → Triple S → Scalar S
schurKernelCovariance S E x y =
  add S
    (add S
      (multiply S
        (rowApply S (r0 E) x)
        (rowApply S (r0 E) y))
      (multiply S
        (rowApply S (r1 E) x)
        (rowApply S (r1 E) y)))
    (multiply S
      (rowApply S (r2 E) x)
      (rowApply S (r2 E) y))

schurDotIsRawKernelCoordinateCovariance :
  (S : ScalarBilinearSurface) →
  (E : Matrix3 S) →
  (x y : Triple S) →
  dot3 S (schurApply S E x) (schurApply S E y)
  ≡ schurKernelCovariance S E x y
schurDotIsRawKernelCoordinateCovariance S E x y = refl

record ThreeTaperSchurKernelBilinearBoundary : Set where
  constructor three-taper-schur-kernel-bilinear-boundary
  field
    fixedSchurMapKeptExplicit : Bool
    fixedSchurMapKeptExplicitIsTrue : fixedSchurMapKeptExplicit ≡ true

    covarianceExpandedInRawThreeTaperCoordinates : Bool
    covarianceExpandedInRawThreeTaperCoordinatesIsTrue :
      covarianceExpandedInRawThreeTaperCoordinates ≡ true

    schurMapReplacedByIdentity : Bool
    schurMapReplacedByIdentityIsFalse :
      schurMapReplacedByIdentity ≡ false

    literalLeanElim2MatrixIdentified : Bool
    literalLeanElim2MatrixIdentifiedIsFalse :
      literalLeanElim2MatrixIdentified ≡ false

    signedKernelCovarianceEstimateClosed : Bool
    signedKernelCovarianceEstimateClosedIsFalse :
      signedKernelCovarianceEstimateClosed ≡ false

canonicalThreeTaperSchurKernelBilinearBoundary :
  ThreeTaperSchurKernelBilinearBoundary
canonicalThreeTaperSchurKernelBilinearBoundary =
  three-taper-schur-kernel-bilinear-boundary
    true refl
    true refl
    false refl
    false refl
    false refl
