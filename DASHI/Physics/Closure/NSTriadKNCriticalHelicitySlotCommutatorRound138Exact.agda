module DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact where

------------------------------------------------------------------------
-- ROUND138 / CRITICAL PRODUCTION AS A HELICITY-SLOT COMMUTATOR
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Constantin--Majda, CMP 115 (1988), DOI 10.1007/BF01218019.
--
-- Round137 shows that complementary helicity classes must be paired before
-- absolute values.  There is a further exact collapse.
--
-- After summing the eight helicity sign channels of one radius triple, the
-- coefficient multiplying a helicity-sign insertion in each slot is
--
--   c_k = r_k (r_p-r_q),
--   c_p = r_p (r_q-r_k),
--   c_q = r_q (r_k-r_p).
--
-- These coefficients satisfy c_k+c_p+c_q = 0 IDENTICALLY.  Hence for arbitrary
-- slot amplitudes B_k,B_p,B_q,
--
--   c_k B_k + c_p B_p + c_q B_q
--     = c_k (B_k-B_q) + c_p (B_p-B_q).
--
-- This is the exact finite algebra behind the next analytic route: critical
-- production only sees DIFFERENCES between helicity-sign insertions in the
-- three slots.  A bound on the individual B's is therefore unnecessarily
-- expensive and destroys a second commutator.
--
-- No estimate is asserted here.  The next physical theorem should identify
-- B_k-B_q and B_p-B_q with differences of the normalized-curl/helicity-sign
-- operator on the literal helical Fourier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

criticalRadialCoefficientK :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
criticalRadialCoefficientK {F = F} rk rp rq =
  C3.multiply F rk (sub rp rq)

criticalRadialCoefficientP :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
criticalRadialCoefficientP {F = F} rk rp rq =
  C3.multiply F rp (sub rq rk)

criticalRadialCoefficientQ :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
criticalRadialCoefficientQ {F = F} rk rp rq =
  C3.multiply F rq (sub rk rp)

criticalRadialCoefficientsSumZero :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq : C3.Carrier F) →
  C3.add F
    (criticalRadialCoefficientK rk rp rq)
    (C3.add F
      (criticalRadialCoefficientP rk rp rq)
      (criticalRadialCoefficientQ rk rp rq))
  ≡ C3.zero F
criticalRadialCoefficientsSumZero {F = F} rk rp rq =
  R.solve 3
    (λ rk rp rq →
      ((rk R.⊗ (rp R.⊕ (R.⊝ rq)))
        R.⊕ ((rp R.⊗ (rq R.⊕ (R.⊝ rk)))
          R.⊕ (rq R.⊗ (rk R.⊕ (R.⊝ rp)))))
      R.⊜ R.Κ (C3.zero F))
    refl rk rp rq
  where module R = Field.Solver F

helicitySlotProduction :
  ∀ {r} {F : C3.RealField r} →
  C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F
helicitySlotProduction {F = F} rk rp rq bk bp bq =
  C3.add F
    (C3.multiply F (criticalRadialCoefficientK rk rp rq) bk)
    (C3.add F
      (C3.multiply F (criticalRadialCoefficientP rk rp rq) bp)
      (C3.multiply F (criticalRadialCoefficientQ rk rp rq) bq))

helicitySlotCommutatorForm :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq bk bp bq : C3.Carrier F) →
  helicitySlotProduction rk rp rq bk bp bq
  ≡ C3.add F
      (C3.multiply F
        (criticalRadialCoefficientK rk rp rq)
        (sub bk bq))
      (C3.multiply F
        (criticalRadialCoefficientP rk rp rq)
        (sub bp bq))
helicitySlotCommutatorForm {F = F} rk rp rq bk bp bq =
  R.solve 6
    (λ rk rp rq bk bp bq →
      (((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ bk)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ bp)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ bq)))
      R.⊜
      ((((rk R.⊗ (rp R.⊕ (R.⊝ rq)))
          R.⊗ (bk R.⊕ (R.⊝ bq)))
        R.⊕
        (((rp R.⊗ (rq R.⊕ (R.⊝ rk)))
          R.⊗ (bp R.⊕ (R.⊝ bq))))) )
    refl rk rp rq bk bp bq
  where module R = Field.Solver F

commonHelicitySlotAmplitudeCancels :
  ∀ {r} {F : C3.RealField r}
    (rk rp rq common : C3.Carrier F) →
  helicitySlotProduction rk rp rq common common common
  ≡ C3.zero F
commonHelicitySlotAmplitudeCancels {F = F} rk rp rq common =
  R.solve 4
    (λ rk rp rq common →
      (((rk R.⊗ (rp R.⊕ (R.⊝ rq))) R.⊗ common)
        R.⊕ (((rp R.⊗ (rq R.⊕ (R.⊝ rk))) R.⊗ common)
          R.⊕ ((rq R.⊗ (rk R.⊕ (R.⊝ rp))) R.⊗ common)))
      R.⊜ R.Κ (C3.zero F))
    refl rk rp rq common
  where module R = Field.Solver F

round138CriticalRadialCoefficientSumZeroClosed : Bool
round138CriticalRadialCoefficientSumZeroClosed = true

round138HelicitySlotDifferenceCommutatorClosed : Bool
round138HelicitySlotDifferenceCommutatorClosed = true

round138IndividualSlotAbsoluteValuesRequired : Bool
round138IndividualSlotAbsoluteValuesRequired = false

round138PhysicalNormalizedCurlSlotDifferenceWeldClosed : Bool
round138PhysicalNormalizedCurlSlotDifferenceWeldClosed = false

round138PackageAClosed : Bool
round138PackageAClosed = false

round138HelicitySlotDifferenceCommutatorClosedIsTrue :
  round138HelicitySlotDifferenceCommutatorClosed ≡ true
round138HelicitySlotDifferenceCommutatorClosedIsTrue = refl

round138PackageAClosedIsFalse : round138PackageAClosed ≡ false
round138PackageAClosedIsFalse = refl
