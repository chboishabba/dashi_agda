module DASHI.Physics.Closure.NSTriadKNNormalizedDoubleMixedCellMassRound452Exact where

------------------------------------------------------------------------
-- ROUND452 / NORMALIZED DOUBLE-MIXED CELL HAS A UNIVERSAL QUADRATIC MASS BOUND
--
-- R174 already proves the exact rational estimate
--
--   ||K(P,Q,a,b)||^2
--     <= 12 ||P+Q||^2 ||a||^2 ||b||^2
--
-- under the R145 transverse-high-pair condition.  For unit normalized
-- directions P,Q,
--
--   ||P+Q||^2 <= 2||P||^2 + 2||Q||^2 = 4.
--
-- Hence
--
--   ||K||^2 <= 48 ||a||^2 ||b||^2.
--
-- R225 identifies the physical double-mixed cell with i times this literal
-- normalized-direction slot kernel.  Multiplication by i preserves the
-- rational C^3 squared norm, so the same 48 bound holds for the actual
-- companion cell.
--
-- This is a pointwise theorem.  No shell count, convolution sum, resolvent
-- weight or time integration is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalComplex3Separation as Separation
import DASHI.Physics.Closure.NSTriadKNPhysicalOrderedTransferSquaredMajorantRound96Exact as R96
import DASHI.Physics.Closure.NSTriadKNAntiParallelHelicitySlotKernelRound145Exact as R145
import DASHI.Physics.Closure.NSTriadKNHHAntiParallelQuadraticKernelNormRound174Exact as R174

F : C3.RealField _
F = Rational.rationalRealField

norm : C3.Complex3 F → ℚ
norm = L2.complex3NormSquared

two four fortyEight : ℚ
two = 1ℚ + 1ℚ
four = two + two
fortyEight = R174.twelve * four

oneNN : 0ℚ ≤ 1ℚ
oneNN = Rational.squareNonnegative 1ℚ

twoNN : 0ℚ ≤ two
twoNN = Rational.addNonnegative oneNN oneNN

fourNN : 0ℚ ≤ four
fourNN = Rational.addNonnegative twoNN twoNN

record UnitDirectionPair (P Q : C3.Complex3 F) : Set where
  constructor unit-direction-pair
  field
    pUnit : norm P ≡ 1ℚ
    qUnit : norm Q ≡ 1ℚ

open UnitDirectionPair public

antiParallelDefectBelowFour :
  (P Q : C3.Complex3 F) →
  UnitDirectionPair P Q →
  norm (R145.antiParallelDefect P Q) ≤ four
antiParallelDefectBelowFour P Q unit =
  let
    raw = R174.normAddBelowTwo P Q
    endpoint : two * norm P + two * norm Q ≡ four
    endpoint rewrite pUnit unit | qUnit unit = solve []
  in
  subst
    (λ upper → norm (R145.antiParallelDefect P Q) ≤ upper)
    endpoint raw

normalizedSlotKernelMassBelowFortyEight :
  (P Q a b : C3.Complex3 F) →
  UnitDirectionPair P Q →
  R145.TransverseHighPair P Q a b →
  norm (R145.slotKernel P Q a b)
  ≤ fortyEight * (norm a * norm b)
normalizedSlotKernelMassBelowFortyEight P Q a b unit transverse =
  let
    sigma = R145.antiParallelDefect P Q
    kernelBound =
      R174.kernelNormBelowTwelveAngularProduct P Q a b transverse
    sigmaBound = antiParallelDefectBelowFour P Q unit
    aNN = Separation.complex3NormSquaredNonnegative a
    bNN = Separation.complex3NormSquaredNonnegative b
    massNN : 0ℚ ≤ norm a * norm b
    massNN = R96.productNonnegative aNN bNN
    sigmaNN = Separation.complex3NormSquaredNonnegative sigma
    scaledSigma :
      norm sigma * (norm a * norm b)
      ≤ four * (norm a * norm b)
    scaledSigma =
      Rational.nonnegativeProductMonotone
        sigmaNN massNN fourNN massNN
        sigmaBound ℚP.≤-refl
    twelveNN : 0ℚ ≤ R174.twelve
    twelveNN =
      let
        six = R174.two + R174.two + R174.two
        sixNN = Rational.addNonnegative
          (Rational.addNonnegative R174.twoNN R174.twoNN)
          R174.twoNN
      in
      Rational.addNonnegative sixNN sixNN
    scaled :
      R174.twelve * (norm sigma * norm a * norm b)
      ≤ R174.twelve * (four * (norm a * norm b))
    scaled =
      let instance twelveNNI = nonNegative twelveNN
      in ℚP.*-monoˡ-≤-nonNeg R174.twelve
        (subst
          (λ lower → lower ≤ four * (norm a * norm b))
          (solve (norm sigma ∷ norm a ∷ norm b ∷ []))
          scaledSigma)
    endpoint :
      R174.twelve * (four * (norm a * norm b))
      ≡ fortyEight * (norm a * norm b)
    endpoint = solve (R174.twelve ∷ four ∷ norm a ∷ norm b ∷ [])
  in
  ℚP.≤-trans kernelBound
    (subst
      (λ upper →
        R174.twelve * (norm sigma * norm a * norm b) ≤ upper)
      endpoint scaled)

iScalePreservesNorm :
  (value : C3.Complex3 F) →
  norm (C3.complex3Scale (C3.complexI F) value) ≡ norm value
iScalePreservesNorm value =
  trans
    (R174.normScale (C3.complexI F) value)
    (cong (_* norm value) iModulusOne)
  where
  iModulusOne :
    L2.complexModulusSquared (C3.complexI F) ≡ 1ℚ
  iModulusOne = solve []

iScaledNormalizedSlotMassBelowFortyEight :
  (P Q a b : C3.Complex3 F) →
  UnitDirectionPair P Q →
  R145.TransverseHighPair P Q a b →
  norm (C3.complex3Scale (C3.complexI F) (R145.slotKernel P Q a b))
  ≤ fortyEight * (norm a * norm b)
iScaledNormalizedSlotMassBelowFortyEight P Q a b unit transverse =
  subst
    (λ lower → lower ≤ fortyEight * (norm a * norm b))
    (sym (iScalePreservesNorm (R145.slotKernel P Q a b)))
    (normalizedSlotKernelMassBelowFortyEight P Q a b unit transverse)

round452UnitNormalizedSlotKernelMassBoundClosed : Bool
round452UnitNormalizedSlotKernelMassBoundClosed = true

round452UniversalPointwiseConstantIsFortyEight : Bool
round452UniversalPointwiseConstantIsFortyEight = true

round452NeedsOnlyUnitDirectionAndTransversality : Bool
round452NeedsOnlyUnitDirectionAndTransversality = true

round452IntroducesCardinalityTax : Bool
round452IntroducesCardinalityTax = false

round452PhysicalNormalizedDirectionUnitLawInstalled : Bool
round452PhysicalNormalizedDirectionUnitLawInstalled = false

round452PackageAClosed : Bool
round452PackageAClosed = false

round452ClayPromotion : Bool
round452ClayPromotion = false

round452IntroducesCardinalityTaxIsFalse : round452IntroducesCardinalityTax ≡ false
round452IntroducesCardinalityTaxIsFalse = refl
