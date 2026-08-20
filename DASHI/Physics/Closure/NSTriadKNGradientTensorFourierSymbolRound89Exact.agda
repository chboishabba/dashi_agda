module DASHI.Physics.Closure.NSTriadKNGradientTensorFourierSymbolRound89Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Author: Loukas Grafakos.
-- Title: "Classical Fourier Analysis".
-- DOI: 10.1007/978-1-4939-1194-3.
--
-- ROUND89 / LITERAL GRADIENT-TENSOR SYMBOL
--
-- On the repository's exact complex Fourier carrier, differentiation in the
-- ell-th coordinate multiplies the p-mode by i p_ell.  Hence for every pair
-- of modes p,q and scalar tensor entry a*b,
--
--   sum_ell [(i p_ell)a][(i q_ell)b]
--      = -(p dot q) (a b).
--
-- This is the exact coefficient identity behind
--
--   Fourier[ sum_ell partial_ell u tensor partial_ell u ](k)
--     = - sum_{p+q=k} (p dot q) u_p tensor u_q.
--
-- The result is pure finite Fourier algebra.  It is the missing bridge needed
-- to move the two high-frequency powers in the Round87 viscous coefficient
-- INSIDE the tensor before applying the existing periodic HH->low H^-1
-- estimate.  No shell majorant, absolute value or continuum limit occurs here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as CRing

gradientSymbol :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Complex F
gradientSymbol {F = F} frequency =
  C3.complexMultiply (C3.complexI F) (C3.realEmbed F frequency)

complexIRealProduct :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Carrier F) →
  C3.complexMultiply
    (gradientSymbol left)
    (gradientSymbol right)
  ≡ C3.complexNegate
      (C3.realEmbed F (C3.multiply F left right))
complexIRealProduct {F = F} left right =
  Algebra.complexExt
    (P.R.solve 2
      (λ a b →
        P.R.⊝ (a P.R.⊗ b)
        P.R.⊜ P.R.⊝ (a P.R.⊗ b))
      refl left right)
    (P.R.solve 2
      (λ a b → P.R.0# P.R.⊜ P.R.0#)
      refl left right)
  where module P = Algebra.Polynomial F

modeGradientDot :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → Z3.FourierMode → C3.Complex F
modeGradientDot {F = F} E p q =
  C3.complexAdd
    (C3.complexAdd
      (C3.complexMultiply
        (gradientSymbol (C3.embedInteger E (Z3.kx p)))
        (gradientSymbol (C3.embedInteger E (Z3.kx q))))
      (C3.complexMultiply
        (gradientSymbol (C3.embedInteger E (Z3.ky p)))
        (gradientSymbol (C3.embedInteger E (Z3.ky q)))))
    (C3.complexMultiply
      (gradientSymbol (C3.embedInteger E (Z3.kz p)))
      (gradientSymbol (C3.embedInteger E (Z3.kz q)))

modeFrequencyDot :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → Z3.FourierMode → C3.Complex F
modeFrequencyDot E p q =
  C3.bilinearDot3 (C3.modeVector E p) (C3.modeVector E q)

modeGradientDotIsNegativeFrequencyDot :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode) →
  modeGradientDot E p q
  ≡ C3.complexNegate (modeFrequencyDot E p q)
modeGradientDotIsNegativeFrequencyDot {F = F} E
    (Z3.mode px py pz) (Z3.mode qx qy qz)
  rewrite complexIRealProduct
    (C3.embedInteger E px) (C3.embedInteger E qx)
        | complexIRealProduct
    (C3.embedInteger E py) (C3.embedInteger E qy)
        | complexIRealProduct
    (C3.embedInteger E pz) (C3.embedInteger E qz) =
  P.solve 6
    (λ x y z X Y Z →
      ((P.⊝ (x P.⊗ X)) P.⊕ (P.⊝ (y P.⊗ Y)))
        P.⊕ (P.⊝ (z P.⊗ Z))
      P.⊜
      P.⊝ (((x P.⊗ X) P.⊕ (y P.⊗ Y)) P.⊕ (z P.⊗ Z)))
    refl
    (C3.realEmbed F (C3.embedInteger E px))
    (C3.realEmbed F (C3.embedInteger E py))
    (C3.realEmbed F (C3.embedInteger E pz))
    (C3.realEmbed F (C3.embedInteger E qx))
    (C3.realEmbed F (C3.embedInteger E qy))
    (C3.realEmbed F (C3.embedInteger E qz))
  where module P = CRing.Solver F

gradientTensorEntry :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex F → C3.Complex F → C3.Complex F
gradientTensorEntry {F = F} E p q left right =
  C3.complexMultiply
    (modeGradientDot E p q)
    (C3.complexMultiply left right)

frequencyWeightedTensorEntry :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex F → C3.Complex F → C3.Complex F
frequencyWeightedTensorEntry {F = F} E p q left right =
  C3.complexNegate
    (C3.complexMultiply
      (modeFrequencyDot E p q)
      (C3.complexMultiply left right))

gradientTensorEntryIsNegativeFrequencyWeightedOuter :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (p q : Z3.FourierMode)
    (left right : C3.Complex F) →
  gradientTensorEntry E p q left right
  ≡ frequencyWeightedTensorEntry E p q left right
gradientTensorEntryIsNegativeFrequencyWeightedOuter {F = F}
    E p q left right =
  trans
    (cong
      (λ coefficient →
        C3.complexMultiply coefficient
          (C3.complexMultiply left right))
      (modeGradientDotIsNegativeFrequencyDot E p q))
    (Algebra.complexNegateMultiplyLeft
      (modeFrequencyDot E p q)
      (C3.complexMultiply left right))

round89GradientTensorFourierSymbolIdentityClosed : Bool
round89GradientTensorFourierSymbolIdentityClosed = true

round89ViscousFrequencyDotIsTwoInputDerivativesExactly : Bool
round89ViscousFrequencyDotIsTwoInputDerivativesExactly = true

round89GradientTensorFourierSymbolIdentityClosedIsTrue :
  round89GradientTensorFourierSymbolIdentityClosed ≡ true
round89GradientTensorFourierSymbolIdentityClosedIsTrue = refl

round89ViscousFrequencyDotIsTwoInputDerivativesExactlyIsTrue :
  round89ViscousFrequencyDotIsTwoInputDerivativesExactly ≡ true
round89ViscousFrequencyDotIsTwoInputDerivativesExactlyIsTrue = refl
