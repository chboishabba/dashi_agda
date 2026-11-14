module DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (trans; cong; cong₂)
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra

------------------------------------------------------------------------
-- B1: true THREE-COMPONENT Maxwell CURL JET on the original C3 field.
-- eps0 = mu0 = c = 1, dt E - curl B + J = 0, dt B + curl E = 0.
-- Pointwise d(|E|²+|B|²)/2 + div(E cross B) + J dot E = 0.
-- A jet is not by itself an analytic spatial field or a boundary integral.
------------------------------------------------------------------------

record R3 {r : Level} (F : C3.RealField r) : Set r where
  constructor r3
  field x y z : C3.Carrier F
open R3 public

zero3 : ∀ {r} (F : C3.RealField r) → R3 F
zero3 F = r3 (C3.zero F) (C3.zero F) (C3.zero F)

add3 : ∀ {r} (F : C3.RealField r) → R3 F → R3 F → R3 F
add3 F a b = r3
  (C3.add F (x a) (x b))
  (C3.add F (y a) (y b))
  (C3.add F (z a) (z b))

negate3 : ∀ {r} (F : C3.RealField r) → R3 F → R3 F
negate3 F a = r3
  (C3.negate F (x a))
  (C3.negate F (y a))
  (C3.negate F (z a))

dot3 : ∀ {r} (F : C3.RealField r) → R3 F → R3 F → C3.Carrier F
dot3 F a b =
  C3.add F
    (C3.multiply F (x a) (x b))
    (C3.add F
      (C3.multiply F (y a) (y b))
      (C3.multiply F (z a) (z b)))

record Jacobian {r : Level} (F : C3.RealField r) : Set r where
  constructor jacobian
  field dx dy dz : R3 F
open Jacobian public

curl3 : ∀ {r} (F : C3.RealField r) → Jacobian F → R3 F
curl3 F D = r3
  (C3.add F (z (dy D)) (C3.negate F (y (dz D))))
  (C3.add F (x (dz D)) (C3.negate F (z (dx D))))
  (C3.add F (y (dx D)) (C3.negate F (x (dy D))))

record FullVectorMaxwellJet {r : Level} (F : C3.RealField r) : Set r where
  constructor full-vector-maxwell-jet
  field
    electric magnetic current dElectricDt dMagneticDt : R3 F
    electricJacobian magneticJacobian : Jacobian F
    ampere :
      add3 F
        (add3 F dElectricDt
          (negate3 F (curl3 F magneticJacobian)))
        current ≡ zero3 F
    faraday :
      add3 F dMagneticDt (curl3 F electricJacobian) ≡ zero3 F
open FullVectorMaxwellJet public

-- Product-rule form div(E cross B) = B dot curl(E) - E dot curl(B).
-- The curls here are actually computed from three directional first jets.
spatialPoyntingDivergence :
  ∀ {r} {F : C3.RealField r} →
  FullVectorMaxwellJet F → C3.Carrier F
spatialPoyntingDivergence {F = F} jet =
  C3.add F
    (dot3 F (magnetic jet) (curl3 F (electricJacobian jet)))
    (C3.negate F
      (dot3 F (electric jet) (curl3 F (magneticJacobian jet))))

fullVectorSignedBudget :
  ∀ {r} {F : C3.RealField r} →
  FullVectorMaxwellJet F → C3.Carrier F
fullVectorSignedBudget {F = F} jet =
  C3.add F
    (C3.add F
      (dot3 F (electric jet) (dElectricDt jet))
      (dot3 F (magnetic jet) (dMagneticDt jet)))
    (C3.add F
      (spatialPoyntingDivergence jet)
      (dot3 F (current jet) (electric jet)))

fullVectorBudgetNormalForm :
  ∀ {r} {F : C3.RealField r} (jet : FullVectorMaxwellJet F) →
  fullVectorSignedBudget jet
  ≡ C3.add F
      (dot3 F (electric jet)
        (add3 F
          (add3 F (dElectricDt jet)
            (negate3 F (curl3 F (magneticJacobian jet))))
          (current jet)))
      (dot3 F (magnetic jet)
        (add3 F (dMagneticDt jet)
          (curl3 F (electricJacobian jet))))
fullVectorBudgetNormalForm {F = F} jet =
  R.solve 21
    (λ ex ey ez bx by bz jx jy jz tx ty tz ux uy uz cx cy cz hx hy hz →
      (((((((ex R.⊗ tx) R.⊕ (ey R.⊗ ty)) R.⊕ (ez R.⊗ tz)) R.⊕ (((bx R.⊗ ux) R.⊕ (by R.⊗ uy)) R.⊕ (bz R.⊗ uz))) R.⊕ (((bx R.⊗ cx) R.⊕ (by R.⊗ cy)) R.⊕ (bz R.⊗ cz))) R.⊕ (R.⊝ (((ex R.⊗ hx) R.⊕ (ey R.⊗ hy)) R.⊕ (ez R.⊗ hz)))) R.⊕ (((jx R.⊗ ex) R.⊕ (jy R.⊗ ey)) R.⊕ (jz R.⊗ ez)))
      R.⊜ ((((ex R.⊗ ((tx R.⊕ (R.⊝ hx)) R.⊕ jx)) R.⊕ (ey R.⊗ ((ty R.⊕ (R.⊝ hy)) R.⊕ jy))) R.⊕ (ez R.⊗ ((tz R.⊕ (R.⊝ hz)) R.⊕ jz))) R.⊕ (((bx R.⊗ (ux R.⊕ cx)) R.⊕ (by R.⊗ (uy R.⊕ cy))) R.⊕ (bz R.⊗ (uz R.⊕ cz)))))
    refl
    (x (electric jet)) (y (electric jet)) (z (electric jet))
    (x (magnetic jet)) (y (magnetic jet)) (z (magnetic jet))
    (x (current jet)) (y (current jet)) (z (current jet))
    (x (dElectricDt jet)) (y (dElectricDt jet)) (z (dElectricDt jet))
    (x (dMagneticDt jet)) (y (dMagneticDt jet)) (z (dMagneticDt jet))
    (x (curl3 F (electricJacobian jet)))
    (y (curl3 F (electricJacobian jet)))
    (z (curl3 F (electricJacobian jet)))
    (x (curl3 F (magneticJacobian jet)))
    (y (curl3 F (magneticJacobian jet)))
    (z (curl3 F (magneticJacobian jet)))
  where module R = Algebra.Solver F

fullVectorMaxwellPoyntingIdentity :
  ∀ {r} {F : C3.RealField r} →
  (jet : FullVectorMaxwellJet F) →
  fullVectorSignedBudget jet ≡ C3.zero F
fullVectorMaxwellPoyntingIdentity {F = F} jet =
  trans (fullVectorBudgetNormalForm jet)
    (trans
      (cong₂ (C3.add F)
        (cong (dot3 F (electric jet)) (ampere jet))
        (cong (dot3 F (magnetic jet)) (faraday jet)))
      (R.solve 6
        (λ ex ey ez bx by bz →
          ((((ex R.⊗ (R.Κ (C3.zero F))) R.⊕ (ey R.⊗ (R.Κ (C3.zero F)))) R.⊕ (ez R.⊗ (R.Κ (C3.zero F)))) R.⊕ (((bx R.⊗ (R.Κ (C3.zero F))) R.⊕ (by R.⊗ (R.Κ (C3.zero F)))) R.⊕ (bz R.⊗ (R.Κ (C3.zero F))))) R.⊜ (R.Κ (C3.zero F)))
        refl
        (x (electric jet)) (y (electric jet)) (z (electric jet))
        (x (magnetic jet)) (y (magnetic jet)) (z (magnetic jet))))
  where module R = Algebra.Solver F

------------------------------------------------------------------------
-- Pointwise algebra CLOSED at a supplied Maxwell derivative jet only.
-- Same original C1 fields, vector product-rule/source compatibility,
-- SI constitutive medium, space-time regularity and actual boundary flux
-- require distinct original U1/integral physical producers.
------------------------------------------------------------------------
