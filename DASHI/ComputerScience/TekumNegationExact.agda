module DASHI.ComputerScience.TekumNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.ComputerScience.TekumAnchorArithmeticExact public
  using (anchorNegationInvariant)
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor

anchoredNegationInvolutive :
  ∀ {n} (x : Anchor.AnchoredTekum n) →
  Anchor.negateAnchored (Anchor.negateAnchored x) ≡ x
anchoredNegationInvolutive = Anchor.negateAnchored-involutive

anchoredNegationKeepsFields :
  ∀ {n} (x : Anchor.AnchoredTekum n) →
  Anchor.anchorFieldsCertified (Anchor.negateAnchored x)
  ≡ Anchor.anchorFieldsCertified x
anchoredNegationKeepsFields (Anchor.anchoredTekum s fields) = refl
