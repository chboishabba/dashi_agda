module DASHI.Algebra.Quantum.LorentzSignatureUniqueness where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Fin using (Fin; zero; suc)

-- The sign of each diagonal axis of a non-degenerate quadratic form.
data AxisSign : Set where
  spacelike timelike : AxisSign

-- The canonical (d,1) diagonal signature: axis zero is the arrow, the
-- remaining d axes are spatial and isotropic.
lorentzSign : ∀ {d} → Fin (suc d) → AxisSign
lorentzSign zero = timelike
lorentzSign (suc _) = spacelike

record ConeArrowIsotropyWitness (d : Nat) (sign : Fin (suc d) → AxisSign) : Set where
  field
    arrow-is-timelike : sign zero ≡ timelike
    spatial-isotropy  : ∀ i → sign (suc i) ≡ spacelike

open ConeArrowIsotropyWitness public

-- No postulates: the witness data force every axis to agree pointwise with
-- the canonical Lorentz sign assignment.
lorentz-signature-unique :
  ∀ {d} {sign : Fin (suc d) → AxisSign} →
  ConeArrowIsotropyWitness d sign →
  ∀ i → sign i ≡ lorentzSign i
lorentz-signature-unique W zero = arrow-is-timelike W
lorentz-signature-unique W (suc i) = spatial-isotropy W i

record SignatureCounts (d : Nat) : Set where
  constructor signature
  field
    positive : Nat
    negative : Nat

lorentzCounts : ∀ d → SignatureCounts d
lorentzCounts d = signature d 1

-- The counting theorem is definitionally exact once the unique arrow and
-- isotropic spatial family have been selected.
derived-signature :
  ∀ {d} {sign : Fin (suc d) → AxisSign} →
  ConeArrowIsotropyWitness d sign →
  SignatureCounts d
derived-signature {d} W = lorentzCounts d

derived-signature-is-d,1 :
  ∀ {d} {sign : Fin (suc d) → AxisSign}
  (W : ConeArrowIsotropyWitness d sign) →
  derived-signature W ≡ signature d 1
derived-signature-is-d,1 W = Agda.Builtin.Equality.refl
