module DASHI.Physics.YangMills.CompactLieBracketBounds where

open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ
  ; 0ℝ
  ; _*ℝ_
  ; _≤ℝ_
  ; ≤ℝ-refl
  ; ≤ℝ-trans
  ; mulMonotoneNonnegative
  )

------------------------------------------------------------------------
-- Quantitative bracket socket over the repository's real-analysis authority.
------------------------------------------------------------------------

record NormedLieBracket (𝔤 : Set) : Set₁ where
  field
    bracket : 𝔤 → 𝔤 → 𝔤
    norm : 𝔤 → ℝ
    bracketConstant : ℝ

    normNonnegative : ∀ X → 0ℝ ≤ℝ norm X
    bracketFactorNonnegative :
      ∀ X → 0ℝ ≤ℝ (bracketConstant *ℝ norm X)

    bracketBound :
      ∀ X Y →
      norm (bracket X Y)
      ≤ℝ
      (bracketConstant *ℝ norm X) *ℝ norm Y

open NormedLieBracket public

iteratedAd :
  ∀ {𝔤 : Set} →
  NormedLieBracket 𝔤 →
  List 𝔤 →
  𝔤 →
  𝔤
iteratedAd data [] Y = Y
iteratedAd data (X ∷ rest) Y =
  bracket data X (iteratedAd data rest Y)

adMajorant :
  ∀ {𝔤 : Set} →
  NormedLieBracket 𝔤 →
  List 𝔤 →
  𝔤 →
  ℝ
adMajorant data [] Y = norm data Y
adMajorant data (X ∷ rest) Y =
  (bracketConstant data *ℝ norm data X) *ℝ
  adMajorant data rest Y

iteratedAdBound :
  ∀ {𝔤 : Set} →
  (data : NormedLieBracket 𝔤) →
  (inputs : List 𝔤) →
  (Y : 𝔤) →
  norm data (iteratedAd data inputs Y)
  ≤ℝ
  adMajorant data inputs Y
iteratedAdBound data [] Y = ≤ℝ-refl
iteratedAdBound data (X ∷ rest) Y =
  ≤ℝ-trans
    (bracketBound data X (iteratedAd data rest Y))
    (mulMonotoneNonnegative
      (bracketFactorNonnegative data X)
      ≤ℝ-refl
      (normNonnegative data (iteratedAd data rest Y))
      (iteratedAdBound data rest Y))
