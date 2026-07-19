module DASHI.Core.RelationalFlowResidualComposition where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Primitive using (Set)

------------------------------------------------------------------------
-- Exact algebraic kernel for composing predictive, semiotic, and governance
-- residuals. Domain modules supply the residual values and threshold proofs;
-- this module proves the generic monotone aggregation step only.

record ResidualArithmetic : Set₁ where
  field
    Residual : Set
    zero : Residual
    _+_ : Residual → Residual → Residual
    _≤_ : Residual → Residual → Set

    +-assoc :
      (a b c : Residual) → (a + b) + c ≡ a + (b + c)

    ≤-refl :
      (a : Residual) → a ≤ a

    ≤-trans :
      {a b c : Residual} → a ≤ b → b ≤ c → a ≤ c

    +-mono-left :
      {a b c : Residual} → a ≤ b → (c + a) ≤ (c + b)

    +-mono-right :
      {a b c : Residual} → a ≤ b → (a + c) ≤ (b + c)

open ResidualArithmetic public

record RelationalResidualInputs (A : ResidualArithmetic) : Set where
  field
    predictiveResidual : Residual A
    semioticResidual : Residual A
    governanceResidual : Residual A
    totalResidual : Residual A

    totalResidualDefinition :
      totalResidual ≡
        (predictiveResidual + semioticResidual) + governanceResidual

open RelationalResidualInputs public

canonicalResidualSum :
  (A : ResidualArithmetic) →
  RelationalResidualInputs A →
  Residual A
canonicalResidualSum A I =
  (predictiveResidual I + semioticResidual I) + governanceResidual I

canonicalResidualSumIsTotal :
  (A : ResidualArithmetic) →
  (I : RelationalResidualInputs A) →
  canonicalResidualSum A I ≡ totalResidual I
canonicalResidualSumIsTotal A I =
  let open RelationalResidualInputs I in
  sym totalResidualDefinition
  where
  sym : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
  sym refl = refl

predictiveBoundLiftsThroughComposition :
  (A : ResidualArithmetic) →
  {p p′ s g : Residual A} →
  p ≤ p′ →
  ((p + s) + g) ≤ ((p′ + s) + g)
predictiveBoundLiftsThroughComposition A p≤p′ =
  +-mono-right A (+-mono-right A p≤p′)

semioticBoundLiftsThroughComposition :
  (A : ResidualArithmetic) →
  {p s s′ g : Residual A} →
  s ≤ s′ →
  ((p + s) + g) ≤ ((p + s′) + g)
semioticBoundLiftsThroughComposition A s≤s′ =
  +-mono-right A (+-mono-left A s≤s′)

governanceBoundLiftsThroughComposition :
  (A : ResidualArithmetic) →
  {p s g g′ : Residual A} →
  g ≤ g′ →
  ((p + s) + g) ≤ ((p + s) + g′)
governanceBoundLiftsThroughComposition A g≤g′ =
  +-mono-left A g≤g′

allThreeBoundsCompose :
  (A : ResidualArithmetic) →
  {p p′ s s′ g g′ : Residual A} →
  p ≤ p′ →
  s ≤ s′ →
  g ≤ g′ →
  ((p + s) + g) ≤ ((p′ + s′) + g′)
allThreeBoundsCompose A p≤p′ s≤s′ g≤g′ =
  ≤-trans A
    (predictiveBoundLiftsThroughComposition A p≤p′)
    (≤-trans A
      (semioticBoundLiftsThroughComposition A s≤s′)
      (governanceBoundLiftsThroughComposition A g≤g′))
