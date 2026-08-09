module DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact where

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
-- DASHI CONTRIBUTION
--
-- Close the algebraic producer that had remained abstract in the exact C3
-- Leray program.  For every nonzero lattice mode k and every v,
--
--   k dot P_k v = 0,
--   P_k(P_k v) = P_k v.
--
-- The proof uses the literal repository definition
--
--   P_k v = v - |k|^{-2} (k dot v) k,
--
-- the exact ModeInverseSquare law, and the already machine-checked complex
-- commutative-ring/additive/scaling identities.  No Hermitian-cutset field is
-- assumed.  This is the concrete transversality theorem needed to show that
-- each projected Galerkin interaction and its finite sum remain in the
-- dependent physical carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as ComplexRing
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3TransverseDifference as Difference
import DASHI.Physics.Closure.NSTriadKNLerayAlgebraProgram as Leray

realEmbedMultiply :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Carrier F) →
  C3.complexMultiply
    (C3.realEmbed F left)
    (C3.realEmbed F right)
  ≡ C3.realEmbed F (C3.multiply F left right)
realEmbedMultiply {F = F} left right =
  Field.complexExt
    (P.R.solve 2
      (λ a b →
        ((a P.R.⊗ b)
          P.R.⊕
          (P.R.⊝
            ((P.R.Κ (C3.zero F))
              P.R.⊗ (P.R.Κ (C3.zero F)))))
        P.R.⊜ (a P.R.⊗ b))
      refl left right)
    (P.R.solve 2
      (λ a b →
        ((a P.R.⊗ (P.R.Κ (C3.zero F)))
          P.R.⊕
          ((P.R.Κ (C3.zero F)) P.R.⊗ b))
        P.R.⊜ P.R.Κ (C3.zero F))
      refl left right)
  where
  module P = Field.Polynomial F

realEmbedAdd :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Carrier F) →
  C3.complexAdd
    (C3.realEmbed F left)
    (C3.realEmbed F right)
  ≡ C3.realEmbed F (C3.add F left right)
realEmbedAdd {F = F} left right =
  Field.complexExt refl (C3.addZeroLeft F (C3.zero F))

modeSelfDotIsEmbeddedNormSquared :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (C3.modeVector E mode)
  ≡ C3.realEmbed F (C3.normSquared I mode)
modeSelfDotIsEmbeddedNormSquared {F = F} E I mode =
  let
    mx = C3.embedInteger E (Z3.kx mode)
    my = C3.embedInteger E (Z3.ky mode)
    mz = C3.embedInteger E (Z3.kz mode)
    xx = C3.multiply F mx mx
    yy = C3.multiply F my my
    zz = C3.multiply F mz mz
  in
  trans
    (cong
      (λ first →
        C3.complexAdd first
          (C3.complexMultiply
            (C3.realEmbed F mz)
            (C3.realEmbed F mz)))
      (cong₂ C3.complexAdd
        (realEmbedMultiply mx mx)
        (realEmbedMultiply my my)))
    (trans
      (cong
        (λ last →
          C3.complexAdd
            (C3.complexAdd
              (C3.realEmbed F xx)
              (C3.realEmbed F yy))
            last)
        (realEmbedMultiply mz mz))
      (trans
        (cong
          (λ first → C3.complexAdd first (C3.realEmbed F zz))
          (realEmbedAdd xx yy))
        (trans
          (realEmbedAdd (C3.add F xx yy) zz)
          (cong (C3.realEmbed F)
            (sym (C3.normSquaredMeaning I mode))))))

embeddedInverseSquareLaw :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  C3.complexMultiply
    (C3.realEmbed F (C3.inverseNormSquared I mode))
    (C3.realEmbed F (C3.normSquared I mode))
  ≡ C3.complexOne F
embeddedInverseSquareLaw {F = F} E I mode nonzero =
  trans
    (realEmbedMultiply
      (C3.inverseNormSquared I mode)
      (C3.normSquared I mode))
    (cong (C3.realEmbed F) (C3.inverseLaw I mode nonzero))

lerayCorrectionHasOriginalLongitudinalPairing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (C3.complex3Scale
      (C3.complexMultiply
        (C3.realEmbed F (C3.inverseNormSquared I mode))
        (C3.bilinearDot3 (C3.modeVector E mode) value))
      (C3.modeVector E mode))
  ≡ C3.bilinearDot3 (C3.modeVector E mode) value
lerayCorrectionHasOriginalLongitudinalPairing
    {F = F} E I mode nonzero value =
  let
    inverse = C3.realEmbed F (C3.inverseNormSquared I mode)
    longitudinal = C3.bilinearDot3 (C3.modeVector E mode) value
    squared = C3.realEmbed F (C3.normSquared I mode)
  in
  trans
    (Scaling.bilinearDot3ScaleRight
      (C3.complexMultiply inverse longitudinal)
      (C3.modeVector E mode)
      (C3.modeVector E mode))
    (trans
      (cong
        (C3.complexMultiply
          (C3.complexMultiply inverse longitudinal))
        (modeSelfDotIsEmbeddedNormSquared E I mode))
      (trans
        (Q.solve 3
          (λ inv dot norm →
            ((inv Q.⊗ dot) Q.⊗ norm)
            Q.⊜ (dot Q.⊗ (inv Q.⊗ norm)))
          refl inverse longitudinal squared)
        (trans
          (cong (C3.complexMultiply longitudinal)
            (embeddedInverseSquareLaw E I mode nonzero))
          (ComplexRing.complexMultiplyOneRight longitudinal))))
  where
  module Q = ComplexRing.Solver F

lerayOutputTransverseExact :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (C3.lerayProject3 E I mode value)
  ≡ C3.complexZero F
lerayOutputTransverseExact {F = F} E I mode nonzero value =
  trans
    (Difference.bilinearDot3SubtractRight
      (C3.modeVector E mode)
      value
      (C3.complex3Scale
        (C3.complexMultiply
          (C3.realEmbed F (C3.inverseNormSquared I mode))
          (C3.bilinearDot3 (C3.modeVector E mode) value))
        (C3.modeVector E mode)))
    (trans
      (cong
        (C3.complexSubtract
          (C3.bilinearDot3 (C3.modeVector E mode) value))
        (lerayCorrectionHasOriginalLongitudinalPairing
          E I mode nonzero value))
      (Additive.complexSubtractSelf
        (C3.bilinearDot3 (C3.modeVector E mode) value)))

lerayIdempotentExact :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (mode : Z3.FourierMode) →
  Z3.NonZeroMode mode →
  (value : C3.Complex3 F) →
  C3.lerayProject3 E I mode
    (C3.lerayProject3 E I mode value)
  ≡ C3.lerayProject3 E I mode value
lerayIdempotentExact E I mode nonzero value =
  Leray.lerayFixesTransverse
    E I mode (C3.lerayProject3 E I mode value)
    (lerayOutputTransverseExact E I mode nonzero value)

lerayOutputTransversalityClosed : Bool
lerayOutputTransversalityClosed = true

lerayIdempotenceClosed : Bool
lerayIdempotenceClosed = true

lerayOutputTransversalityClosedIsTrue :
  lerayOutputTransversalityClosed ≡ true
lerayOutputTransversalityClosedIsTrue = refl

lerayIdempotenceClosedIsTrue :
  lerayIdempotenceClosed ≡ true
lerayIdempotenceClosedIsTrue = refl
