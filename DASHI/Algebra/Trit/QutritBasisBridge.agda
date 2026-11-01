module DASHI.Algebra.Trit.QutritBasisBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit
open import DASHI.Algebra.Quantum.FiniteQutrit

------------------------------------------------------------------------
-- Classical trits correspond exactly to qutrit basis labels.
--
-- This is not an identification of Trit with arbitrary qutrit state vectors:
-- coherent superpositions and phases live outside the classical carrier.

tritToQutritBasis : Trit → QutritBasis
tritToQutritBasis neg = ket0
tritToQutritBasis zer = ket1
tritToQutritBasis pos = ket2

qutritBasisToTrit : QutritBasis → Trit
qutritBasisToTrit ket0 = neg
qutritBasisToTrit ket1 = zer
qutritBasisToTrit ket2 = pos

qutritBasisAfterTrit :
  (t : Trit) →
  qutritBasisToTrit (tritToQutritBasis t) ≡ t
qutritBasisAfterTrit neg = refl
qutritBasisAfterTrit zer = refl
qutritBasisAfterTrit pos = refl

tritAfterQutritBasis :
  (q : QutritBasis) →
  tritToQutritBasis (qutritBasisToTrit q) ≡ q
tritAfterQutritBasis ket0 = refl
tritAfterQutritBasis ket1 = refl
tritAfterQutritBasis ket2 = refl

record TritQutritBasisEquivalence : Set where
  field
    toBasis : Trit → QutritBasis
    fromBasis : QutritBasis → Trit
    fromAfterTo : (t : Trit) → fromBasis (toBasis t) ≡ t
    toAfterFrom : (q : QutritBasis) → toBasis (fromBasis q) ≡ q

open TritQutritBasisEquivalence public

canonicalTritQutritBasisEquivalence : TritQutritBasisEquivalence
canonicalTritQutritBasisEquivalence =
  record
    { toBasis = tritToQutritBasis
    ; fromBasis = qutritBasisToTrit
    ; fromAfterTo = qutritBasisAfterTrit
    ; toAfterFrom = tritAfterQutritBasis
    }
