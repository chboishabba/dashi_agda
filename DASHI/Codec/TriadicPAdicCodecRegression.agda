module DASHI.Codec.TriadicPAdicCodecRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Codec.TriadicPAdicCodec

sheetWitness : Sheet9
sheetWitness = sheet neg pos

kernelWitness : Kernel (suc zero)
kernelWitness = zer ∷ᵥ []ᵥ

liftWitness : Kernel (suc (suc (suc zero)))
liftWitness = lift9 sheetWitness kernelWitness

liftWitness-shape :
  liftWitness ≡ neg ∷ᵥ pos ∷ᵥ zer ∷ᵥ []ᵥ
liftWitness-shape = refl

fold-neg-roundtrip : unfoldTrit (foldTrit neg) ≡ neg
fold-neg-roundtrip = refl

fold-zero-roundtrip : unfoldTrit (foldTrit zer) ≡ zer
fold-zero-roundtrip = refl

fold-pos-roundtrip : unfoldTrit (foldTrit pos) ≡ pos
fold-pos-roundtrip = refl

support-zero-fixed : support zer ≡ false
support-zero-fixed = refl

support-neg-active : support neg ≡ true
support-neg-active = refl

support-pos-active : support pos ≡ true
support-pos-active = refl

inversionWitness : invertKernel (invertKernel liftWitness) ≡ liftWitness
inversionWitness = invertKernel-invol liftWitness

sheetLiftInversionWitness :
  invertKernel (lift9 sheetWitness kernelWitness)
  ≡
  lift9 (invertKernel sheetWitness) (invertKernel kernelWitness)
sheetLiftInversionWitness =
  lift9-inversion-compatible sheetWitness kernelWitness

fiveTritWitness : FiveTrits
fiveTritWitness = five neg zer pos neg pos

-- 0 + 3 * (1 + 3 * (2 + 3 * (0 + 3 * 2))) = 183.
-- This is a representation witness only; byte boundedness and decoder
-- roundtrip remain in Pack5Contract until an executable bounded-Nat carrier is
-- connected.
encode5Witness : encode5 fiveTritWitness ≡ 183
encode5Witness = refl

boundaryFiniteCarrierChecked :
  TriadicPAdicCodecBoundary.finiteTritCarrierChecked canonicalBoundary ≡ true
boundaryFiniteCarrierChecked = refl

boundaryLosslessTyped :
  TriadicPAdicCodecBoundary.losslessContractTyped canonicalBoundary ≡ true
boundaryLosslessTyped = refl

boundaryNoAV1Promotion :
  TriadicPAdicCodecBoundary.av1SuperiorityProvedHere canonicalBoundary ≡ false
boundaryNoAV1Promotion = refl

boundaryNoSiliconSpeedupPromotion :
  TriadicPAdicCodecBoundary.physicalSiliconSpeedupProvedHere canonicalBoundary
  ≡ false
boundaryNoSiliconSpeedupPromotion = refl
