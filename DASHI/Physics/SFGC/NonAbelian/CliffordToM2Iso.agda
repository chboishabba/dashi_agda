module DASHI.Physics.SFGC.NonAbelian.CliffordToM2Iso where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.SFGC.NonAbelian.CliffordEvenSubalgebra using
  (EvenBasis; one; e12; e23; e13)
import DASHI.Physics.Closure.TriadicMatrixGenerationTheorem as TMG

------------------------------------------------------------------------
-- Basis-level witness between the even Clifford basis and the triadic M2 basis.
--
-- This is intentionally finite and explicit.  It packages the basis bijection
-- that the rest of the repo already uses as a bridge object.

cliffordToM2Basis : EvenBasis → TMG.M2BasisElement
cliffordToM2Basis one = TMG.e11
cliffordToM2Basis e12 = TMG.e12
cliffordToM2Basis e23 = TMG.e21
cliffordToM2Basis e13 = TMG.e22

m2ToCliffordBasis : TMG.M2BasisElement → EvenBasis
m2ToCliffordBasis TMG.e11 = one
m2ToCliffordBasis TMG.e12 = e12
m2ToCliffordBasis TMG.e21 = e23
m2ToCliffordBasis TMG.e22 = e13

record CliffordM2BasisIso : Set where
  field
    toM2 :
      EvenBasis → TMG.M2BasisElement

    fromM2 :
      TMG.M2BasisElement → EvenBasis

    toFrom :
      ∀ m →
      toM2 (fromM2 m) ≡ m

    fromTo :
      ∀ b →
      fromM2 (toM2 b) ≡ b

canonicalCliffordM2BasisIso :
  CliffordM2BasisIso
canonicalCliffordM2BasisIso =
  record
    { toM2 = cliffordToM2Basis
    ; fromM2 = m2ToCliffordBasis
    ; toFrom = λ where
        TMG.e11 → refl
        TMG.e12 → refl
        TMG.e21 → refl
        TMG.e22 → refl
    ; fromTo = λ where
        one → refl
        e12 → refl
        e23 → refl
        e13 → refl
    }

open CliffordM2BasisIso public
