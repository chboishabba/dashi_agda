module DASHI.ComputerScience.TekumNegationExact where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.ComputerScience.TekumAnchorArithmeticExact as Arithmetic
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor

anchorNegationInvariant = Arithmetic.anchorNegationInvariant

anchoredNegationInvolutive :
  ∀ {n} (x : Anchor.AnchoredTekum n) →
  Anchor.negateAnchored (Anchor.negateAnchored x) ≡ x
anchoredNegationInvolutive = Anchor.negateAnchored-involutive

anchoredNegationKeepsFields :
  ∀ {n} (x : Anchor.AnchoredTekum n) →
  Anchor.anchorFieldsCertified (Anchor.negateAnchored x)
  ≡ Anchor.anchorFieldsCertified x
anchoredNegationKeepsFields (Anchor.anchoredTekum s fields) = refl
