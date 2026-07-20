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
iteratedAd bundle [] Y = Y
iteratedAd bundle (X ∷ rest) Y =
  bracket bundle X (iteratedAd bundle rest Y)

adMajorant :
  ∀ {𝔤 : Set} →
  NormedLieBracket 𝔤 →
  List 𝔤 →
  𝔤 →
  ℝ
adMajorant bundle [] Y = norm bundle Y
adMajorant bundle (X ∷ rest) Y =
  (bracketConstant bundle *ℝ norm bundle X) *ℝ
  adMajorant bundle rest Y

iteratedAdBound :
  ∀ {𝔤 : Set} →
  (bundle : NormedLieBracket 𝔤) →
  (inputs : List 𝔤) →
  (Y : 𝔤) →
  norm bundle (iteratedAd bundle inputs Y)
  ≤ℝ
  adMajorant bundle inputs Y
iteratedAdBound bundle [] Y = ≤ℝ-refl
iteratedAdBound bundle (X ∷ rest) Y =
  ≤ℝ-trans
    (bracketBound bundle X (iteratedAd bundle rest Y))
    (mulMonotoneNonnegative
      (bracketFactorNonnegative bundle X)
      ≤ℝ-refl
      (normNonnegative bundle (iteratedAd bundle rest Y))
      (iteratedAdBound bundle rest Y))
