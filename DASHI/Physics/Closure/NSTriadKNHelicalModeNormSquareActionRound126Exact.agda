module DASHI.Physics.Closure.NSTriadKNHelicalModeNormSquareActionRound126Exact where

------------------------------------------------------------------------
-- ROUND126 / HELICAL MODE-NORM SQUARE ACTION IS NOT AN EXTRA AXIOM
--
-- The periodic helical infrastructure exposes both
--
--   curl^2 h = |k|^2 h
--
-- on transverse vectors and
--
--   curl h^+ =  m(k) h^+,
--   curl h^- = -m(k) h^-.
--
-- The record did not separately state m(k)^2 = |k|^2.  Rather than add that
-- scalar identity as a new authority, derive the exact vector ACTION identity
-- from the existing laws.  This is enough to show that on every actual helical
-- component the squared helical eigenvalue acts exactly as the physical
-- Fourier norm square.
--
-- No scalar cancellation is used.  Consequently this theorem remains valid on
-- the repository's deliberately weak algebraic RealField carrier, which does
-- not assume an integral-domain cancellation law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNProjectedNonlinearityFirstVariationRound82Exact as Linear
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as Tangent

curlSymbolScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (scalar : C3.Complex F)
    (value : C3.Complex3 F) →
  Helical.curlSymbol E k (C3.complex3Scale scalar value)
  ≡ C3.complex3Scale scalar (Helical.curlSymbol E k value)
curlSymbolScale {F = F} E k scalar value =
  trans
    (cong
      (C3.complex3Scale (C3.complexI F))
      (Tangent.crossScaleRight scalar (C3.modeVector E k) value))
    (trans
      (Linear.complex3ScaleAssociative
        (C3.complexI F) scalar (Helical.complex3Cross (C3.modeVector E k) value))
      (trans
        (cong
          (λ coefficient →
            C3.complex3Scale coefficient
              (Helical.complex3Cross (C3.modeVector E k) value))
          (R.solve 2
            (λ i s → (i R.⊗ s) R.⊜ (s R.⊗ i))
            refl (C3.complexI F) scalar))
        (sym
          (Linear.complex3ScaleAssociative
            scalar (C3.complexI F)
            (Helical.complex3Cross (C3.modeVector E k) value)))))
  where module R = Ring.Solver F

realSquare :
  ∀ {r} {F : C3.RealField r} → C3.Carrier F → C3.Carrier F
realSquare {F = F} x = C3.multiply F x x

realEmbedSquareMultiply :
  ∀ {r} {F : C3.RealField r}
    (x : C3.Carrier F) →
  C3.complexMultiply (C3.realEmbed F x) (C3.realEmbed F x)
  ≡ C3.realEmbed F (realSquare x)
realEmbedSquareMultiply {F = F} x =
  Field.complexExt
    (R.solve 1
      (λ x →
        ((x R.⊗ x) R.⊕
          (R.⊝ (R.Κ (C3.zero F) R.⊗ R.Κ (C3.zero F))))
        R.⊜ x R.⊗ x)
      refl x)
    (R.solve 1
      (λ x →
        ((x R.⊗ R.Κ (C3.zero F)) R.⊕
          (R.Κ (C3.zero F) R.⊗ x))
        R.⊜ R.Κ (C3.zero F))
      refl x)
  where module R = Ring.Solver F

minusRealSquareMultiply :
  ∀ {r} {F : C3.RealField r}
    (x : C3.Carrier F) →
  C3.complexMultiply
    (C3.realEmbed F (C3.negate F x))
    (C3.realEmbed F (C3.negate F x))
  ≡ C3.realEmbed F (realSquare x)
minusRealSquareMultiply {F = F} x =
  Field.complexExt
    (R.solve 1
      (λ x →
        (((R.⊝ x) R.⊗ (R.⊝ x)) R.⊕
          (R.⊝ (R.Κ (C3.zero F) R.⊗ R.Κ (C3.zero F))))
        R.⊜ x R.⊗ x)
      refl x)
    (R.solve 1
      (λ x →
        (((R.⊝ x) R.⊗ R.Κ (C3.zero F)) R.⊕
          (R.Κ (C3.zero F) R.⊗ (R.⊝ x)))
        R.⊜ R.Κ (C3.zero F))
      refl x)
  where module R = Ring.Solver F

plusHelicalModeNormSquareActsAsPhysicalNormSquare :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (laws : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.realEmbed F (realSquare (Helical.modeNorm S k)))
    (Helical.helicalProjectorPlus E I S k value)
  ≡
  C3.complex3Scale
    (C3.realEmbed F (C3.normSquared I k))
    (Helical.helicalProjectorPlus E I S k value)
plusHelicalModeNormSquareActsAsPhysicalNormSquare {F = F} {E = E} {I = I}
    S laws k value =
  let
    h = Helical.helicalProjectorPlus E I S k value
    m = Helical.modeNorm S k
    eigen = Helical.helicalCurlEigenvaluePlus laws k value
    transverse = Helical.helicalProjectorDivergenceFree laws Helical.plus k value
    squared = Helical.curlSymbolSquaredOnTransverse laws k h transverse
    nested :
      C3.complex3Scale (C3.realEmbed F m)
        (C3.complex3Scale (C3.realEmbed F m) h)
      ≡ C3.complex3Scale
          (C3.realEmbed F (C3.normSquared I k)) h
    nested =
      trans
        (cong (C3.complex3Scale (C3.realEmbed F m)) (sym eigen))
        (trans
          (sym (curlSymbolScale E k (C3.realEmbed F m) h))
          (trans
            (cong (Helical.curlSymbol E k) (sym eigen))
            squared))
  in
  trans
    (cong
      (λ coefficient → C3.complex3Scale coefficient h)
      (sym (realEmbedSquareMultiply m)))
    (trans
      (sym
        (Linear.complex3ScaleAssociative
          (C3.realEmbed F m) (C3.realEmbed F m) h))
      nested)

minusHelicalModeNormSquareActsAsPhysicalNormSquare :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (S : Helical.HelicalModeScalars F)
    (laws : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.realEmbed F (realSquare (Helical.modeNorm S k)))
    (Helical.helicalProjectorMinus E I S k value)
  ≡
  C3.complex3Scale
    (C3.realEmbed F (C3.normSquared I k))
    (Helical.helicalProjectorMinus E I S k value)
minusHelicalModeNormSquareActsAsPhysicalNormSquare {F = F} {E = E} {I = I}
    S laws k value =
  let
    h = Helical.helicalProjectorMinus E I S k value
    m = Helical.modeNorm S k
    minusM = C3.negate F m
    eigen = Helical.helicalCurlEigenvalueMinus laws k value
    transverse = Helical.helicalProjectorDivergenceFree laws Helical.minus k value
    squared = Helical.curlSymbolSquaredOnTransverse laws k h transverse
    nested :
      C3.complex3Scale (C3.realEmbed F minusM)
        (C3.complex3Scale (C3.realEmbed F minusM) h)
      ≡ C3.complex3Scale
          (C3.realEmbed F (C3.normSquared I k)) h
    nested =
      trans
        (cong (C3.complex3Scale (C3.realEmbed F minusM)) (sym eigen))
        (trans
          (sym (curlSymbolScale E k (C3.realEmbed F minusM) h))
          (trans
            (cong (Helical.curlSymbol E k) (sym eigen))
            squared))
  in
  trans
    (cong
      (λ coefficient → C3.complex3Scale coefficient h)
      (sym (minusRealSquareMultiply m)))
    (trans
      (sym
        (Linear.complex3ScaleAssociative
          (C3.realEmbed F minusM) (C3.realEmbed F minusM) h))
      nested)

round126CurlScalarLinearityClosed : Bool
round126CurlScalarLinearityClosed = true

round126HelicalModeNormSquareActionClosed : Bool
round126HelicalModeNormSquareActionClosed = true

round126ScalarModeNormSquareEqualityClaimed : Bool
round126ScalarModeNormSquareEqualityClaimed = false

round126OrderedRealRadialGapTransportClosed : Bool
round126OrderedRealRadialGapTransportClosed = false

round126HelicalModeNormSquareActionClosedIsTrue :
  round126HelicalModeNormSquareActionClosed ≡ true
round126HelicalModeNormSquareActionClosedIsTrue = refl

round126ScalarModeNormSquareEqualityClaimedIsFalse :
  round126ScalarModeNormSquareEqualityClaimed ≡ false
round126ScalarModeNormSquareEqualityClaimedIsFalse = refl

round126OrderedRealRadialGapTransportClosedIsFalse :
  round126OrderedRealRadialGapTransportClosed ≡ false
round126OrderedRealRadialGapTransportClosedIsFalse = refl
