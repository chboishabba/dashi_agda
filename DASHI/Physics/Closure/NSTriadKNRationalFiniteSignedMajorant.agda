module DASHI.Physics.Closure.NSTriadKNRationalFiniteSignedMajorant where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Augustin-Louis Cauchy; Agda standard-library contributors; DASHI
-- repository contributors.
-- Title: "Finite two-sided triangle majorant for rational shell kernels".
-- Venue/year: Cauchy's finite-sum triangle inequality; Agda standard library;
-- DASHI formal development, 2026.
-- DOI: not applicable to the classical finite-sum result or this
-- repository-specialised formalisation.
-- Uses: monotonicity of finite rational sums and the stronger termwise
-- two-sided estimate -M(j,d) <= T(j,d) <= M(j,d).
-- Relationship: proves directly that every finite signed shell rectangle is
-- trapped between plus and minus the corresponding positive-majorant sum.
-- It avoids requiring a separate absolute-value API.  The concrete
-- Navier--Stokes coefficient still has to be mapped to such a termwise
-- two-sided estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; -_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality as Eq
  using (cong; subst)
open Eq.≡-Reasoning

import DASHI.Physics.Closure.NSTriadKNOutputRelocationPositiveKernelMajorant as Majorant

sumToCong : ∀ left right cutoff →
  (∀ index → left index ≡ right index) →
  Majorant.sumTo left cutoff ≡ Majorant.sumTo right cutoff
sumToCong left right zero pointwise = pointwise zero
sumToCong left right (suc cutoff) pointwise =
  cong₂ _+_
    (pointwise (suc cutoff))
    (sumToCong left right cutoff pointwise)
  where
  cong₂ : ∀ {a b c d : ℚ} →
    a ≡ b → c ≡ d → a + c ≡ b + d
  cong₂ refl refl = refl

sumToNeg : ∀ values cutoff →
  Majorant.sumTo (λ index → - values index) cutoff
  ≡ - Majorant.sumTo values cutoff
sumToNeg values zero = refl
sumToNeg values (suc cutoff) =
  begin
    Majorant.sumTo (λ index → - values index) (suc cutoff)
  ≡⟨ cong
       (λ rest → - values (suc cutoff) + rest)
       (sumToNeg values cutoff) ⟩
    - values (suc cutoff) + (- Majorant.sumTo values cutoff)
  ≡⟨ solve (values (suc cutoff) ∷ Majorant.sumTo values cutoff ∷ []) ⟩
    - Majorant.sumTo values (suc cutoff)
  ∎

rowSumNeg : ∀ kernel lowShell gapCutoff →
  Majorant.rowSum
    (λ low gap → - kernel low gap) lowShell gapCutoff
  ≡ - Majorant.rowSum kernel lowShell gapCutoff
rowSumNeg kernel lowShell gapCutoff =
  sumToNeg (kernel lowShell) gapCutoff

rectangleSumNeg : ∀ kernel lowCutoff gapCutoff →
  Majorant.rectangleSum
    (λ low gap → - kernel low gap) lowCutoff gapCutoff
  ≡ - Majorant.rectangleSum kernel lowCutoff gapCutoff
rectangleSumNeg kernel lowCutoff gapCutoff =
  begin
    Majorant.rectangleSum
      (λ low gap → - kernel low gap) lowCutoff gapCutoff
  ≡⟨ sumToCong
       (λ low →
         Majorant.rowSum (λ left gap → - kernel left gap)
           low gapCutoff)
       (λ low → - Majorant.rowSum kernel low gapCutoff)
       lowCutoff
       (λ low → rowSumNeg kernel low gapCutoff) ⟩
    Majorant.sumTo
      (λ low → - Majorant.rowSum kernel low gapCutoff)
      lowCutoff
  ≡⟨ sumToNeg
       (λ low → Majorant.rowSum kernel low gapCutoff)
       lowCutoff ⟩
    - Majorant.rectangleSum kernel lowCutoff gapCutoff
  ∎

rectangleSumMonotone : ∀ left right lowCutoff gapCutoff →
  (∀ low gap → left low gap ≤ right low gap) →
  Majorant.rectangleSum left lowCutoff gapCutoff
  ≤ Majorant.rectangleSum right lowCutoff gapCutoff
rectangleSumMonotone left right lowCutoff gapCutoff pointwise =
  Majorant.sumToMonotone
    (λ low → Majorant.rowSum left low gapCutoff)
    (λ low → Majorant.rowSum right low gapCutoff)
    lowCutoff
    (λ low →
      Majorant.sumToMonotone
        (left low) (right low) gapCutoff (pointwise low))

record SignedKernelMajorized : Set where
  constructor signed-majorized
  field
    signedKernel positiveMajorant : Nat → Nat → ℚ
    termUpper : ∀ low gap →
      signedKernel low gap ≤ positiveMajorant low gap
    termLower : ∀ low gap →
      - positiveMajorant low gap ≤ signedKernel low gap

open SignedKernelMajorized public

signedRectangleUpper : ∀ S lowCutoff gapCutoff →
  Majorant.rectangleSum (signedKernel S) lowCutoff gapCutoff
  ≤ Majorant.rectangleSum (positiveMajorant S) lowCutoff gapCutoff
signedRectangleUpper S lowCutoff gapCutoff =
  rectangleSumMonotone
    (signedKernel S) (positiveMajorant S)
    lowCutoff gapCutoff (termUpper S)

signedRectangleLower : ∀ S lowCutoff gapCutoff →
  - Majorant.rectangleSum (positiveMajorant S) lowCutoff gapCutoff
  ≤ Majorant.rectangleSum (signedKernel S) lowCutoff gapCutoff
signedRectangleLower S lowCutoff gapCutoff =
  let
    pointwiseLower :
      Majorant.rectangleSum
        (λ low gap → - positiveMajorant S low gap)
        lowCutoff gapCutoff
      ≤ Majorant.rectangleSum (signedKernel S) lowCutoff gapCutoff
    pointwiseLower =
      rectangleSumMonotone
        (λ low gap → - positiveMajorant S low gap)
        (signedKernel S)
        lowCutoff gapCutoff (termLower S)
  in
  subst
    (λ lower →
      lower ≤ Majorant.rectangleSum (signedKernel S) lowCutoff gapCutoff)
    (rectangleSumNeg
      (positiveMajorant S) lowCutoff gapCutoff)
    pointwiseLower

record UniformSignedKernelBound : Set where
  constructor uniform-bound
  field
    signedFamily : SignedKernelMajorized
    uniformConstant : ℚ
    majorantCutoffBound : ∀ lowCutoff gapCutoff →
      Majorant.rectangleSum
        (positiveMajorant signedFamily) lowCutoff gapCutoff
      ≤ uniformConstant

open UniformSignedKernelBound public

uniformSignedUpper : ∀ U lowCutoff gapCutoff →
  Majorant.rectangleSum
    (signedKernel (signedFamily U)) lowCutoff gapCutoff
  ≤ uniformConstant U
uniformSignedUpper U lowCutoff gapCutoff =
  ℚₚ.≤-trans
    (signedRectangleUpper (signedFamily U) lowCutoff gapCutoff)
    (majorantCutoffBound U lowCutoff gapCutoff)

uniformSignedLower : ∀ U lowCutoff gapCutoff →
  - uniformConstant U
  ≤ Majorant.rectangleSum
      (signedKernel (signedFamily U)) lowCutoff gapCutoff
uniformSignedLower U lowCutoff gapCutoff =
  let
    majorantBound = majorantCutoffBound U lowCutoff gapCutoff
    negatedBound :
      - uniformConstant U
      ≤ - Majorant.rectangleSum
          (positiveMajorant (signedFamily U)) lowCutoff gapCutoff
    negatedBound = ℚₚ.neg-antimono-≤ majorantBound
  in
  ℚₚ.≤-trans
    negatedBound
    (signedRectangleLower (signedFamily U) lowCutoff gapCutoff)

finiteSignedMajorantTheoremClosed : Bool
finiteSignedMajorantTheoremClosed = true

finiteTwoSidedTriangleDominationClosed : Bool
finiteTwoSidedTriangleDominationClosed = true

concreteOutputRelocationSignedKernelMapped : Bool
concreteOutputRelocationSignedKernelMapped = false

finiteSignedMajorantTheoremClosedIsTrue :
  finiteSignedMajorantTheoremClosed ≡ true
finiteSignedMajorantTheoremClosedIsTrue = refl

finiteTwoSidedTriangleDominationClosedIsTrue :
  finiteTwoSidedTriangleDominationClosed ≡ true
finiteTwoSidedTriangleDominationClosedIsTrue = refl

concreteOutputRelocationSignedKernelMappedIsFalse :
  concreteOutputRelocationSignedKernelMapped ≡ false
concreteOutputRelocationSignedKernelMappedIsFalse = refl
