module DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegFieldRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- Authors: Peter Constantin; Andrew Majda.
-- Title: "The Beltrami spectrum for incompressible fluid flows".
-- DOI: 10.1007/BF01218019.
--
-- ROUND102 / REALFIELD HETEROCHIRAL MINORITY-LEG NORMAL FORM
--
-- Source-native lifting of the rational Round102 sign exhaustion to the same
-- arbitrary RealField carrier used by the literal Round93 Fourier/Waleffe
-- factorization.
--
-- For positive radius symbols rk,rp,rq (positivity is not needed for the
-- polynomial identities themselves) and common triad amplitude A, define
--
--   Tk=(lambda_q-lambda_p)A,
--   Tp=(lambda_k-lambda_q)A,
--   Tq=(lambda_p-lambda_k)A,
--   Xdot=rk Tk+rp Tp+rq Tq.
--
-- The two homochiral sign classes have Xdot=0.  Every mixed class is exactly
-- twice the critical-weighted transfer of its unique minority-helicity leg.
-- In difference normal form, when k is minority,
--
--   Xdot = +/- 2 rk (rq-rp) A,
--
-- with cyclic analogues for p and q.  Thus the six heterochiral sign classes
-- reduce to three cyclic geometric cases without division or order axioms.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two : ∀ {r : Level} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

record WaleffeCriticalFieldCell {r : Level} (F : C3.RealField r) : Set r where
  constructor waleffe-critical-field-cell
  field
    radiusK radiusP radiusQ amplitude : C3.Carrier F

open WaleffeCriticalFieldCell public

transferK :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
transferK {F = F} lambdaP lambdaQ A =
  C3.multiply F (sub lambdaQ lambdaP) A

transferP :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
transferP {F = F} lambdaK lambdaQ A =
  C3.multiply F (sub lambdaK lambdaQ) A

transferQ :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
transferQ {F = F} lambdaP lambdaK A =
  C3.multiply F (sub lambdaP lambdaK) A

criticalProduction :
  ∀ {r} {F : C3.RealField r} →
  WaleffeCriticalFieldCell F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
criticalProduction {F = F} C lambdaK lambdaP lambdaQ =
  C3.add F
    (C3.multiply F (radiusK C) (transferK lambdaP lambdaQ (amplitude C)))
    (C3.add F
      (C3.multiply F (radiusP C) (transferP lambdaK lambdaQ (amplitude C)))
      (C3.multiply F (radiusQ C) (transferQ lambdaP lambdaK (amplitude C))))

homochiralPlusVanishes :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C (radiusK C) (radiusP C) (radiusQ C) ≡ C3.zero F
homochiralPlusVanishes {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ ((q P.R.⊕ P.R.⊝ p) P.R.⊗ A))
       P.R.⊕ ((p P.R.⊗ ((k P.R.⊕ P.R.⊝ q) P.R.⊗ A))
       P.R.⊕ (q P.R.⊗ ((p P.R.⊕ P.R.⊝ k) P.R.⊗ A))))
      P.R.⊜ P.R.K (C3.zero F))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

homochiralMinusVanishes :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (C3.negate F (radiusK C))
    (C3.negate F (radiusP C))
    (C3.negate F (radiusQ C))
  ≡ C3.zero F
homochiralMinusVanishes {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ (((P.R.⊝ q) P.R.⊕ P.R.⊝ (P.R.⊝ p)) P.R.⊗ A))
       P.R.⊕ ((p P.R.⊗ (((P.R.⊝ k) P.R.⊕ P.R.⊝ (P.R.⊝ q)) P.R.⊗ A))
       P.R.⊕ (q P.R.⊗ (((P.R.⊝ p) P.R.⊕ P.R.⊝ (P.R.⊝ k)) P.R.⊗ A))))
      P.R.⊜ P.R.K (C3.zero F))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityKMinusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (C3.negate F (radiusK C)) (radiusP C) (radiusQ C)
  ≡ C3.multiply F
      (C3.multiply F
        (C3.multiply F (two F) (radiusK C))
        (sub (radiusQ C) (radiusP C)))
      (amplitude C)
minorityKMinusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ ((q P.R.⊕ P.R.⊝ p) P.R.⊗ A))
       P.R.⊕ ((p P.R.⊗ (((P.R.⊝ k) P.R.⊕ P.R.⊝ q) P.R.⊗ A))
       P.R.⊕ (q P.R.⊗ ((p P.R.⊕ P.R.⊝ (P.R.⊝ k)) P.R.⊗ A))))
      P.R.⊜
      ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ k)
        P.R.⊗ (q P.R.⊕ P.R.⊝ p)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityKPlusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (radiusK C) (C3.negate F (radiusP C)) (C3.negate F (radiusQ C))
  ≡ C3.negate F
      (C3.multiply F
        (C3.multiply F
          (C3.multiply F (two F) (radiusK C))
          (sub (radiusQ C) (radiusP C)))
        (amplitude C))
minorityKPlusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ (((P.R.⊝ q) P.R.⊕ P.R.⊝ (P.R.⊝ p)) P.R.⊗ A))
       P.R.⊕ (((P.R.⊝ p) P.R.⊗ ((k P.R.⊕ P.R.⊝ (P.R.⊝ q)) P.R.⊗ A))
       P.R.⊕ ((P.R.⊝ q) P.R.⊗ (((P.R.⊝ p) P.R.⊕ P.R.⊝ k) P.R.⊗ A))))
      P.R.⊜
      P.R.⊝ ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ k)
        P.R.⊗ (q P.R.⊕ P.R.⊝ p)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityPMinusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (radiusK C) (C3.negate F (radiusP C)) (radiusQ C)
  ≡ C3.multiply F
      (C3.multiply F
        (C3.multiply F (two F) (radiusP C))
        (sub (radiusK C) (radiusQ C)))
      (amplitude C)
minorityPMinusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ ((q P.R.⊕ P.R.⊝ (P.R.⊝ p)) P.R.⊗ A))
       P.R.⊕ (((P.R.⊝ p) P.R.⊗ ((k P.R.⊕ P.R.⊝ q) P.R.⊗ A))
       P.R.⊕ (q P.R.⊗ (((P.R.⊝ p) P.R.⊕ P.R.⊝ k) P.R.⊗ A))))
      P.R.⊜
      ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ p)
        P.R.⊗ (k P.R.⊕ P.R.⊝ q)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityPPlusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (C3.negate F (radiusK C)) (radiusP C) (C3.negate F (radiusQ C))
  ≡ C3.negate F
      (C3.multiply F
        (C3.multiply F
          (C3.multiply F (two F) (radiusP C))
          (sub (radiusK C) (radiusQ C)))
        (amplitude C))
minorityPPlusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ (((P.R.⊝ q) P.R.⊕ P.R.⊝ p) P.R.⊗ A))
       P.R.⊕ ((p P.R.⊗ (((P.R.⊝ k) P.R.⊕ P.R.⊝ (P.R.⊝ q)) P.R.⊗ A))
       P.R.⊕ ((P.R.⊝ q) P.R.⊗ ((p P.R.⊕ P.R.⊝ (P.R.⊝ k)) P.R.⊗ A))))
      P.R.⊜
      P.R.⊝ ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ p)
        P.R.⊗ (k P.R.⊕ P.R.⊝ q)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityQMinusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (radiusK C) (radiusP C) (C3.negate F (radiusQ C))
  ≡ C3.multiply F
      (C3.multiply F
        (C3.multiply F (two F) (radiusQ C))
        (sub (radiusP C) (radiusK C)))
      (amplitude C)
minorityQMinusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ (((P.R.⊝ q) P.R.⊕ P.R.⊝ p) P.R.⊗ A))
       P.R.⊕ ((p P.R.⊗ ((k P.R.⊕ P.R.⊝ (P.R.⊝ q)) P.R.⊗ A))
       P.R.⊕ ((P.R.⊝ q) P.R.⊗ ((p P.R.⊕ P.R.⊝ k) P.R.⊗ A))))
      P.R.⊜
      ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ q)
        P.R.⊗ (p P.R.⊕ P.R.⊝ k)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

minorityQPlusDifferenceNormalForm :
  ∀ {r} {F : C3.RealField r} (C : WaleffeCriticalFieldCell F) →
  criticalProduction C
    (C3.negate F (radiusK C)) (C3.negate F (radiusP C)) (radiusQ C)
  ≡ C3.negate F
      (C3.multiply F
        (C3.multiply F
          (C3.multiply F (two F) (radiusQ C))
          (sub (radiusP C) (radiusK C)))
        (amplitude C))
minorityQPlusDifferenceNormalForm {F = F} C =
  P.R.solve 4
    (λ k p q A →
      ((k P.R.⊗ ((q P.R.⊕ P.R.⊝ (P.R.⊝ p)) P.R.⊗ A))
       P.R.⊕ (((P.R.⊝ p) P.R.⊗ (((P.R.⊝ k) P.R.⊕ P.R.⊝ q) P.R.⊗ A))
       P.R.⊕ (q P.R.⊗ (((P.R.⊝ p) P.R.⊕ P.R.⊝ (P.R.⊝ k)) P.R.⊗ A))))
      P.R.⊜
      P.R.⊝ ((((P.R.K (C3.one F) P.R.⊕ P.R.K (C3.one F)) P.R.⊗ q)
        P.R.⊗ (p P.R.⊕ P.R.⊝ k)) P.R.⊗ A))
    refl (radiusK C) (radiusP C) (radiusQ C) (amplitude C)
  where module P = Field.Polynomial F

round102RealFieldMinorityLegNormalFormClosed : Bool
round102RealFieldMinorityLegNormalFormClosed = true

round102RealFieldMinorityLegNormalFormClosedIsTrue :
  round102RealFieldMinorityLegNormalFormClosed ≡ true
round102RealFieldMinorityLegNormalFormClosedIsTrue = refl
