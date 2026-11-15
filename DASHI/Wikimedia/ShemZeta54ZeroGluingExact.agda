module DASHI.Wikimedia.ShemZeta54ZeroGluingExact where

-- DASHI follow-up to its original Zeta54/AlbertPair53 chart.
-- A proposed *equivariant quotient* DIFFERENT from deleting only one
-- zeta-sheet origin.  Source-written; Agda kernel receipt is OPEN.
-- Reuse the two-sided 27 <-> 1+26 source owner.
-- No Monster/VOA representation recognition is implied by this chart.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Cube
import DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact as Zeta
import DASHI.Wikimedia.IbrahimTernary27OriginTraceless26AlbertShapeBidiExact as Shape
import DASHI.Wikimedia.IbrahimZeta54AlbertPair53SnowballAttributionBidiExact as Original

-- 54=2*27: quotient the two centres into ONE shared zero.
-- 53=1+2*26: phase is only meaningful in the nonzero fibre.
data ZeroGlued53 : Set where
  zero53 : ZeroGlued53
  positive53 negative53 : Shape.NonOrigin26 → ZeroGlued53

phaseSwap : Zeta.Zeta54Site → Zeta.Zeta54Site
phaseSwap (Zeta.zeta54Site Zeta.zetaSheet p) =
  Zeta.zeta54Site Zeta.inverseZetaSheet p
phaseSwap (Zeta.zeta54Site Zeta.inverseZetaSheet p) =
  Zeta.zeta54Site Zeta.zetaSheet p

phaseSwapInvolutive : (s : Zeta.Zeta54Site) → phaseSwap (phaseSwap s) ≡ s
phaseSwapInvolutive (Zeta.zeta54Site Zeta.zetaSheet p) = refl
phaseSwapInvolutive (Zeta.zeta54Site Zeta.inverseZetaSheet p) = refl

swapGlued : ZeroGlued53 → ZeroGlued53
swapGlued zero53 = zero53
swapGlued (positive53 q) = negative53 q
swapGlued (negative53 q) = positive53 q

swapGluedInvolutive : (s : ZeroGlued53) → swapGlued (swapGlued s) ≡ s
swapGluedInvolutive zero53 = refl
swapGluedInvolutive (positive53 q) = refl
swapGluedInvolutive (negative53 q) = refl

glue : Zeta.Zeta54Site → ZeroGlued53
glue (Zeta.zeta54Site Zeta.zetaSheet p) with Shape.toAlbertShape p
... | inj₁ scalar = zero53
... | inj₂ q = positive53 q
glue (Zeta.zeta54Site Zeta.inverseZetaSheet p) with Shape.toAlbertShape p
... | inj₁ scalar = zero53
... | inj₂ q = negative53 q

glueCommutesWithConjugation :
  (s : Zeta.Zeta54Site) → glue (phaseSwap s) ≡ swapGlued (glue s)
glueCommutesWithConjugation (Zeta.zeta54Site Zeta.zetaSheet p)
  with Shape.toAlbertShape p
... | inj₁ scalar = refl
... | inj₂ q = refl
glueCommutesWithConjugation (Zeta.zeta54Site Zeta.inverseZetaSheet p)
  with Shape.toAlbertShape p
... | inj₁ scalar = refl
... | inj₂ q = refl

-- Original ZetaResidual53 is an asymmetric deletion presentation.
-- A chosen chart between two 53-element carriers may transport the
-- quotient involution, but does not turn it into *original pure phase
-- exchange restricted to the deleted subset*.
fromDeletion : Original.ZetaResidual53 → ZeroGlued53
fromDeletion (inj₁ q) = positive53 q
fromDeletion (inj₂ p) with Shape.toAlbertShape p
... | inj₁ scalar = zero53
... | inj₂ q = negative53 q

toDeletion : ZeroGlued53 → Original.ZetaResidual53
toDeletion zero53 = inj₂ Cube.origin
toDeletion (positive53 q) = inj₁ q
toDeletion (negative53 q) = inj₂ (Shape.nonOriginToPoint q)

swapDeletionTransported : Original.ZetaResidual53 → Original.ZetaResidual53
swapDeletionTransported s = toDeletion (swapGlued (fromDeletion s))

-- Remaining Agda proof obligations:
-- (a) toDeletion (fromDeletion s) = s via Shape.fromAfterTo,
-- (b) fromDeletion (toDeletion s) = s via Shape.toAfterFrom,
-- (c) transported swap is involutive, then same-action admission separately.
