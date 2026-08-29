module DASHI.Physics.YangMills.BalabanDifferentiatedMarkedFactorProductExact where

------------------------------------------------------------------------
-- ROUND72: FACTORWISE MARKED CMP109 ESTIMATES -> WHOLE DIFFERENTIATED PRODUCT
--
-- PRIMARY SOURCE CALIBRATION
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99(3) (1985), 389--434.
-- DOI: 10.1007/BF01240355.
-- Theorem 3.14/(3.154) is the marked domain-difference input for the changed
-- propagator/background factor.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
-- Equations (4.3)--(4.5) express the already differentiated activity through
-- finite tree/factor expressions with ordinary exponential tree bounds.
--
-- DASHI CONTRIBUTION
--
-- Remove a remaining whole-term receipt from Lemma 7.  Suppose each source
-- factor has ordinary majorant b_i on BOTH domains and its domain replacement
-- has marked majorant m_i:
--
--   |f_i| <= b_i,   |g_i| <= b_i,   |f_i-g_i| <= m_i.
--
-- Then the entire finite differentiated product obeys the exact telescope
-- majorant
--
--   |prod f - prod g|
--     <= m_1 b_2 ... b_n
--       + b_1 m_2 b_3 ... b_n
--       + ...
--       + b_1 ... b_{n-1} m_n.
--
-- Hence the Yang--Mills-specific producer no longer needs to bound complete
-- replacement terms.  It supplies only the literal factorwise ordinary/marked
-- estimates from CMP99(3)/CMP109; finite assembly is proved here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; 1ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; absℝ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; +-mono-≤ ; absZero ; absAddSubadditive ; absMul
  ; mulMonotoneNonnegative ; subSelf )
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Hess
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Standard ordered-real absolute-value facts missing from the intentionally
-- minimal RealAnalysisAxioms surface.  They are not Yang--Mills assumptions.
------------------------------------------------------------------------

postulate
  absNonnegative : ∀ x → 0ℝ ≤ℝ absℝ x
  absOne : absℝ 1ℝ ≡ 1ℝ

------------------------------------------------------------------------
-- Ordinary product majorant.
------------------------------------------------------------------------

absProductBelowProductMajorant :
  {A : Set} →
  (f b : A → ℝ) →
  (xs : List A) →
  (∀ x → 0ℝ ≤ℝ b x) →
  (∀ x → absℝ (f x) ≤ℝ b x) →
  absℝ (Hess.productℝ f xs) ≤ℝ Hess.productℝ b xs
absProductBelowProductMajorant f b [] b≥0 factorBound
  rewrite absOne = ≤ℝ-refl
absProductBelowProductMajorant f b (x ∷ xs) b≥0 factorBound
  rewrite absMul (f x) (Hess.productℝ f xs) =
  mulMonotoneNonnegative
    (absNonnegative (f x))
    (factorBound x)
    (absNonnegative (Hess.productℝ f xs))
    (absProductBelowProductMajorant f b xs b≥0 factorBound)

------------------------------------------------------------------------
-- Exact telescoping majorant generated from factorwise marked estimates.
------------------------------------------------------------------------

markedProductMajorant :
  {A : Set} →
  (ordinary marked : A → ℝ) →
  List A → ℝ
markedProductMajorant ordinary marked [] = 0ℝ
markedProductMajorant ordinary marked (x ∷ xs) =
  marked x *ℝ Hess.productℝ ordinary xs
  +ℝ ordinary x *ℝ markedProductMajorant ordinary marked xs

markedProductDifferenceFromFactorwiseBounds :
  {A : Set} →
  (f g ordinary marked : A → ℝ) →
  (xs : List A) →
  (∀ x → 0ℝ ≤ℝ ordinary x) →
  (∀ x → absℝ (f x) ≤ℝ ordinary x) →
  (∀ x → absℝ (g x) ≤ℝ ordinary x) →
  (∀ x → absℝ (f x -ℝ g x) ≤ℝ marked x) →
  absℝ (Hess.productℝ f xs -ℝ Hess.productℝ g xs)
    ≤ℝ
  markedProductMajorant ordinary marked xs
markedProductDifferenceFromFactorwiseBounds
  f g ordinary marked [] ordinary≥0 fBound gBound markedBound
  rewrite subSelf 1ℝ | absZero = ≤ℝ-refl
markedProductDifferenceFromFactorwiseBounds
  f g ordinary marked (x ∷ xs) ordinary≥0 fBound gBound markedBound
  rewrite Hess.productHeadTelescope
      (f x) (g x) (Hess.productℝ f xs) (Hess.productℝ g xs) =
  let
    tailProductBound = absProductBelowProductMajorant
      f ordinary xs ordinary≥0 fBound

    markedHeadProductBound :
      absℝ ((f x -ℝ g x) *ℝ Hess.productℝ f xs)
      ≤ℝ
      marked x *ℝ Hess.productℝ ordinary xs
    markedHeadProductBound
      rewrite absMul (f x -ℝ g x) (Hess.productℝ f xs) =
      mulMonotoneNonnegative
        (absNonnegative (f x -ℝ g x))
        (markedBound x)
        (absNonnegative (Hess.productℝ f xs))
        tailProductBound

    tailDifferenceBound = markedProductDifferenceFromFactorwiseBounds
      f g ordinary marked xs ordinary≥0 fBound gBound markedBound

    unchangedHeadTimesTailBound :
      absℝ (g x *ℝ
        (Hess.productℝ f xs -ℝ Hess.productℝ g xs))
      ≤ℝ
      ordinary x *ℝ markedProductMajorant ordinary marked xs
    unchangedHeadTimesTailBound
      rewrite absMul (g x)
        (Hess.productℝ f xs -ℝ Hess.productℝ g xs) =
      mulMonotoneNonnegative
        (absNonnegative (g x))
        (gBound x)
        (absNonnegative
          (Hess.productℝ f xs -ℝ Hess.productℝ g xs))
        tailDifferenceBound
  in
  ≤ℝ-trans
    (absAddSubadditive
      ((f x -ℝ g x) *ℝ Hess.productℝ f xs)
      (g x *ℝ (Hess.productℝ f xs -ℝ Hess.productℝ g xs)))
    (+-mono-≤ markedHeadProductBound unchangedHeadTimesTailBound)

factorwiseMarkedProductAssemblyLevel : ProofLevel
factorwiseMarkedProductAssemblyLevel = machineChecked

-- Physical Lemma 7 seam after this theorem:
-- instantiate `ordinary` and `marked` with the ACTUAL CMP109 differentiated
-- tree factors.  The marked factor gets CMP99(3) distance-to-discrepancy decay;
-- the unchanged factors retain ordinary CMP109 tree decay.  CMP116 then sums
-- the resulting majorant over localization/tree families.
physicalCMP109FactorwiseOrdinaryAndMarkedBoundsLevel : ProofLevel
physicalCMP109FactorwiseOrdinaryAndMarkedBoundsLevel = conditional
