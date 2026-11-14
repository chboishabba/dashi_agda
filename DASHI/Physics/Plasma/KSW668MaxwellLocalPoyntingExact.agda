module DASHI.Physics.Plasma.KSW668MaxwellLocalPoyntingExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra

------------------------------------------------------------------------
-- B1: physical one-dimensional transverse Maxwell jet.
-- E=E_y(x,t), B=B_z(x,t), J=J_y(x,t), eps0=mu0=c=1.
-- Maxwell/Faraday:
--   ∂t E + ∂x B + J = 0
--   ∂t B + ∂x E = 0
-- Divergences vanish because fields depend only on x and have y/z components.
-- The jets are actual local first derivative coordinates, not spatial
-- integration or independently derived differentiable functions.
------------------------------------------------------------------------

record TransverseMaxwellJet
    {r : Level} (F : C3.RealField r) : Set r where
  constructor transverse-maxwell-jet
  field
    ey bz jy dtEy dtBz dxEy dxBz : C3.Carrier F
    ampere :
      C3.add F dtEy (C3.add F dxBz jy) ≡ C3.zero F
    faraday :
      C3.add F dtBz dxEy ≡ C3.zero F

open TransverseMaxwellJet public

private
  _+F_ : ∀ {r} {F : C3.RealField r} →
          C3.Carrier F → C3.Carrier F → C3.Carrier F
  _+F_ {F = F} = C3.add F

poyntingRate :
  ∀ {r} {F : C3.RealField r} →
  TransverseMaxwellJet F → C3.Carrier F
poyntingRate {F = F} jet =
  C3.add F
    (C3.add F
      (C3.multiply F (ey jet) (dtEy jet))
      (C3.multiply F (bz jet) (dtBz jet)))
    (C3.add F
      (C3.multiply F (dxEy jet) (bz jet))
      (C3.multiply F (ey jet) (dxBz jet)))

totalSignedWorkBudget :
  ∀ {r} {F : C3.RealField r} →
  TransverseMaxwellJet F → C3.Carrier F
totalSignedWorkBudget {F = F} jet =
  C3.add F
    (poyntingRate jet)
    (C3.multiply F (jy jet) (ey jet))

-- Exactly the first derivatives of
-- u=(E_y^2+B_z^2)/2 and S_x=E_y B_z. No division by 2 is needed.
poyntingRateNormalForm :
  ∀ {r} {F : C3.RealField r} →
  (jet : TransverseMaxwellJet F) →
  totalSignedWorkBudget jet
  ≡ C3.add F
      (C3.multiply F (ey jet)
        (C3.add F (dtEy jet)
          (C3.add F (dxBz jet) (jy jet))))
      (C3.multiply F (bz jet)
        (C3.add F (dtBz jet) (dxEy jet)))
poyntingRateNormalForm {F = F} jet =
  R.solve 7
    (λ e b j et bt ex bx →
      (((e R.⊗ et) R.⊕ (b R.⊗ bt))
        R.⊕ ((ex R.⊗ b) R.⊕ (e R.⊗ bx))
        R.⊕ (j R.⊗ e))
      R.⊜
      ((e R.⊗ (et R.⊕ (bx R.⊕ j)))
        R.⊕ (b R.⊗ (bt R.⊕ ex))))
    refl (ey jet) (bz jet) (jy jet)
      (dtEy jet) (dtBz jet) (dxEy jet) (dxBz jet)
  where module R = Algebra.Solver F

originalMaxwellDifferentialPoyntingFromU1 :
  ∀ {r} {F : C3.RealField r} →
  (jet : TransverseMaxwellJet F) →
  totalSignedWorkBudget jet ≡ C3.zero F
originalMaxwellDifferentialPoyntingFromU1 {F = F} jet =
  trans
    (poyntingRateNormalForm jet)
    (trans
      (cong₂ (C3.add F)
        (cong (C3.multiply F (ey jet)) (ampere jet))
        (cong (C3.multiply F (bz jet)) (faraday jet)))
      (R.solve 2
        (λ e b →
          ((e R.⊗ R.Κ (C3.zero F))
            R.⊕ (b R.⊗ R.Κ (C3.zero F)))
          R.⊜ R.Κ (C3.zero F))
        refl (ey jet) (bz jet)))
  where module R = Algebra.Solver F

------------------------------------------------------------------------
-- B2: the divergence theorem/time differentiation of an integral are
-- separate analytic producers. The executable exact polynomial slab
-- evaluates both faces and the complete volume energy/work.
------------------------------------------------------------------------
