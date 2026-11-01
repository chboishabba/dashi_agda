module DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Augustin-Louis Cauchy; Hermann Amandus Schwarz.
-- Result: finite-dimensional Cauchy--Schwarz inequality.
-- DOI: not applicable to the original nineteenth-century results.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND96 / LITERAL COEFFICIENT-TO-CUBIC-MASS ATOM
--
-- The exact ordered physical transfer has the transverse normal form
--
--   T_kpq = Re[-i (u_p . q) <u_k,u_q>].
--
-- On the exact rational C3 carrier, two sharp Cauchy inequalities and
-- multiplicativity of complex modulus give the radical-free theorem
--
--   T_kpq^2
--     <= |q|^2 ||u_k||_2^2 ||u_p||_2^2 ||u_q||_2^2.
--
-- Here |q|^2 is the literal `ModeInverseSquare.normSquared` value.  No
-- positive-part replacement, shell counting, Bernstein estimate, or hidden
-- Leray norm appears.  This is the pointwise coefficient majorant needed before
-- Round91's Bony/cubic-charge aggregation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNRationalComplex3HermitianCauchyRound74Exact as HC
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3OrderedRealityCancellation as Ordered
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38

F : C3.RealField _
F = Rational.rationalRealField

square : ℚ → ℚ
square x = x * x

productNonnegative : ∀ {a b : ℚ} →
  0ℚ ≤ a → 0ℚ ≤ b → 0ℚ ≤ a * b
productNonnegative {a} {b} aNN bNN =
  let
    instance
      aNNI = nonNegative aNN
      bNNI = nonNegative bNN
      abNNI = ℚP.nonNeg*nonNeg⇒nonNeg a b
  in
  ℚP.nonNegative⁻¹ (a * b)

complexModulusProduct : ∀ a b →
  L2.complexModulusSquared (C3.complexMultiply a b)
  ≡ L2.complexModulusSquared a * L2.complexModulusSquared b
complexModulusProduct
    (C3.complex ar ai) (C3.complex br bi) =
  solve (ar ∷ ai ∷ br ∷ bi ∷ [])

minusIModulusInvariant : ∀ z →
  L2.complexModulusSquared
    (C3.complexMultiply (Ordered.minusI F) z)
  ≡ L2.complexModulusSquared z
minusIModulusInvariant (C3.complex zr zi) =
  solve (zr ∷ zi ∷ [])

realCoordinateSquareBelowModulus : ∀ z →
  square (C3.real z) ≤ L2.complexModulusSquared z
realCoordinateSquareBelowModulus (C3.complex zr zi) =
  let
    imagNN = Rational.squareNonnegative zi
    shifted = ℚP.+-monoʳ-≤ (square zr) imagNN
  in
  subst
    (λ lower → lower ≤ square zr + square zi)
    (sym (ℚP.+-identityʳ (square zr)))
    shifted

complexModulusConjugateInvariant : ∀ z →
  L2.complexModulusSquared (C3.complexConjugate z)
  ≡ L2.complexModulusSquared z
complexModulusConjugateInvariant (C3.complex zr zi) =
  solve (zr ∷ zi ∷ [])

complex3NormConjugateInvariant : ∀ u →
  L2.complex3NormSquared (C3.complex3Conjugate u)
  ≡ L2.complex3NormSquared u
complex3NormConjugateInvariant (C3.complex3 ux uy uz)
  rewrite complexModulusConjugateInvariant ux
        | complexModulusConjugateInvariant uy
        | complexModulusConjugateInvariant uz = refl

bilinearDotAsHermitianConjugateLeft : ∀ u v →
  C3.bilinearDot3 u v
  ≡ C3.hermitianPairing3 (C3.complex3Conjugate u) v
bilinearDotAsHermitianConjugateLeft u v =
  sym
    (cong
      (λ first → C3.bilinearDot3 first v)
      (C3.complex3ConjugateInvolutive u))

rationalBilinearDotCauchy : ∀ u v →
  L2.complexModulusSquared (C3.bilinearDot3 u v)
  ≤ L2.complex3NormSquared u * L2.complex3NormSquared v
rationalBilinearDotCauchy u v =
  let
    base = HC.rationalComplex3HermitianCauchy
      (C3.complex3Conjugate u) v

    lowerMeaning :
      L2.complexModulusSquared (C3.bilinearDot3 u v)
      ≡ L2.complexModulusSquared
          (C3.hermitianPairing3 (C3.complex3Conjugate u) v)
    lowerMeaning =
      cong L2.complexModulusSquared
        (bilinearDotAsHermitianConjugateLeft u v)

    upperMeaning :
      L2.complex3NormSquared (C3.complex3Conjugate u)
        * L2.complex3NormSquared v
      ≡ L2.complex3NormSquared u * L2.complex3NormSquared v
    upperMeaning =
      cong
        (λ left → left * L2.complex3NormSquared v)
        (complex3NormConjugateInvariant u)
  in
  subst
    (λ lower → lower ≤
      L2.complex3NormSquared u * L2.complex3NormSquared v)
    (sym lowerMeaning)
    (subst
      (λ upper →
        L2.complexModulusSquared
          (C3.hermitianPairing3 (C3.complex3Conjugate u) v)
        ≤ upper)
      upperMeaning base)

modeVectorNormSquaredMeaning :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (mode : Z3.FourierMode) →
  L2.complex3NormSquared (C3.modeVector E mode)
  ≡ C3.normSquared I mode
modeVectorNormSquaredMeaning E I (Z3.mode kx ky kz) =
  let
    mx = C3.embedInteger E kx
    my = C3.embedInteger E ky
    mz = C3.embedInteger E kz

    expanded :
      L2.complex3NormSquared
        (C3.modeVector E (Z3.mode kx ky kz))
      ≡ (mx * mx + my * my) + mz * mz
    expanded = solve (mx ∷ my ∷ mz ∷ [])
  in
  trans expanded (sym (C3.normSquaredMeaning I (Z3.mode kx ky kz)))

orderedTransferSquaredMajorant :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (tau : Physical.PhysicalTriadIncidence) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.DivergenceFreeCondition E velocity →
  square (Round38.orderedPower E I tau velocity)
  ≤ C3.normSquared I (Physical.q tau)
      * L2.complex3NormSquared (velocity (Physical.k tau))
      * L2.complex3NormSquared (velocity (Physical.p tau))
      * L2.complex3NormSquared (velocity (Physical.q tau))
orderedTransferSquaredMajorant E I tau velocity divergenceFree =
  let
    uK = velocity (Physical.k tau)
    uP = velocity (Physical.p tau)
    uQ = velocity (Physical.q tau)
    waveQ = C3.modeVector E (Physical.q tau)
    wave = C3.bilinearDot3 uP waveQ
    pair = C3.hermitianPairing3 uK uQ
    product = C3.complexMultiply wave pair
    z = C3.complexMultiply (Ordered.minusI F) product

    normalComplex =
      Ordered.orderedTransferNormalForm E I tau velocity divergenceFree

    transferMeaning :
      Round38.orderedPower E I tau velocity
      ≡ C3.real z
    transferMeaning = cong C3.real normalComplex

    transferSquareToRealSquare :
      square (Round38.orderedPower E I tau velocity)
      ≡ square (C3.real z)
    transferSquareToRealSquare = cong square transferMeaning

    realBelowModulus : square (C3.real z) ≤ L2.complexModulusSquared z
    realBelowModulus = realCoordinateSquareBelowModulus z

    zModulusMeaning :
      L2.complexModulusSquared z
      ≡ L2.complexModulusSquared wave * L2.complexModulusSquared pair
    zModulusMeaning =
      trans
        (minusIModulusInvariant product)
        (complexModulusProduct wave pair)

    waveCauchy :
      L2.complexModulusSquared wave
      ≤ L2.complex3NormSquared uP * L2.complex3NormSquared waveQ
    waveCauchy = rationalBilinearDotCauchy uP waveQ

    pairCauchy :
      L2.complexModulusSquared pair
      ≤ L2.complex3NormSquared uK * L2.complex3NormSquared uQ
    pairCauchy = HC.rationalComplex3HermitianCauchy uK uQ

    waveNN = Separation.complexModulusSquaredNonnegative wave
    pairNN = Separation.complexModulusSquaredNonnegative pair
    uPNN = Separation.complex3NormSquaredNonnegative uP
    waveQNN = Separation.complex3NormSquaredNonnegative waveQ
    uKNN = Separation.complex3NormSquaredNonnegative uK
    uQNN = Separation.complex3NormSquaredNonnegative uQ

    waveUpperNN = productNonnegative uPNN waveQNN
    pairUpperNN = productNonnegative uKNN uQNN

    productCauchy :
      L2.complexModulusSquared wave * L2.complexModulusSquared pair
      ≤ (L2.complex3NormSquared uP * L2.complex3NormSquared waveQ)
        * (L2.complex3NormSquared uK * L2.complex3NormSquared uQ)
    productCauchy =
      Rational.nonnegativeProductMonotone
        waveNN pairNN waveUpperNN pairUpperNN waveCauchy pairCauchy

    modeNorm = C3.normSquared I (Physical.q tau)
    uKNorm = L2.complex3NormSquared uK
    uPNorm = L2.complex3NormSquared uP
    uQNorm = L2.complex3NormSquared uQ

    rearranged :
      (uPNorm * L2.complex3NormSquared waveQ) * (uKNorm * uQNorm)
      ≡ modeNorm * uKNorm * uPNorm * uQNorm
    rearranged =
      subst
        (λ qNorm →
          (uPNorm * qNorm) * (uKNorm * uQNorm)
          ≡ modeNorm * uKNorm * uPNorm * uQNorm)
        (sym (modeVectorNormSquaredMeaning E I (Physical.q tau)))
        (solve (modeNorm ∷ uKNorm ∷ uPNorm ∷ uQNorm ∷ []))

    modulusToFinal :
      L2.complexModulusSquared z
      ≤ modeNorm * uKNorm * uPNorm * uQNorm
    modulusToFinal =
      subst
        (λ lower → lower ≤ modeNorm * uKNorm * uPNorm * uQNorm)
        (sym zModulusMeaning)
        (subst
          (λ upper →
            L2.complexModulusSquared wave * L2.complexModulusSquared pair
            ≤ upper)
          rearranged productCauchy)
  in
  subst
    (λ lower → lower ≤ modeNorm * uKNorm * uPNorm * uQNorm)
    (sym transferSquareToRealSquare)
    (ℚP.≤-trans realBelowModulus modulusToFinal)

round96LiteralOrderedTransferSquaredMajorantConstructed : Bool
round96LiteralOrderedTransferSquaredMajorantConstructed = true

round96LiteralOrderedTransferSquaredMajorantConstructedIsTrue :
  round96LiteralOrderedTransferSquaredMajorantConstructed ≡ true
round96LiteralOrderedTransferSquaredMajorantConstructedIsTrue = refl
