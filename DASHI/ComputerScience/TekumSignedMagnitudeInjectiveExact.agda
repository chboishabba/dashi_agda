module DASHI.ComputerScience.TekumSignedMagnitudeInjectiveExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; -_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor

------------------------------------------------------------------------
-- A positive magnitude plus a nonzero external sign is injective.
------------------------------------------------------------------------

data OrdinarySign : Anchor.TekumSign → Set where
  negative : OrdinarySign Anchor.negativeSign
  positive : OrdinarySign Anchor.positiveSign

negativePositiveDistinct :
  ∀ {m n : ℚ} →
  0ℚ ℚ.< m → 0ℚ ℚ.< n →
  (ℚ.- m) ≡ n →
  Data.Empty.⊥
negativePositiveDistinct mPositive nPositive eq =
  ℚP.<⇒≢
    (ℚP.<-trans (ℚP.neg-antimono-< mPositive) nPositive)
    eq

positiveNegativeDistinct :
  ∀ {m n : ℚ} →
  0ℚ ℚ.< m → 0ℚ ℚ.< n →
  m ≡ (ℚ.- n) →
  Data.Empty.⊥
positiveNegativeDistinct mPositive nPositive eq =
  negativePositiveDistinct nPositive mPositive (sym eq)

signedPositiveInjective :
  ∀ {s t : Anchor.TekumSign} {m n : ℚ} →
  OrdinarySign s → OrdinarySign t →
  0ℚ ℚ.< m → 0ℚ ℚ.< n →
  Factor.applyRationalSign s m ≡ Factor.applyRationalSign t n →
  (s ≡ t) × (m ≡ n)
signedPositiveInjective negative negative mPositive nPositive eq =
  refl , ℚP.neg-injective eq
signedPositiveInjective negative positive mPositive nPositive eq =
  ⊥-elim (negativePositiveDistinct mPositive nPositive eq)
signedPositiveInjective positive negative mPositive nPositive eq =
  ⊥-elim (positiveNegativeDistinct mPositive nPositive eq)
signedPositiveInjective positive positive mPositive nPositive eq =
  refl , eq
