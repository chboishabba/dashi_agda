module DASHI.Physics.YangMills.BalabanCMP102BishopOriginalFiniteRowAggregateExact where

-- Exact finite-row extensionality on the ORIGINAL CMP102 signed terms.
-- No new Bishop sum or Cauchy operator. The two pointwise source
-- identifications remain explicit proof inputs; they are NOT assumed
-- consequences of factorial pair identities without bounded index transport.
-- Attribution: Murray/Csimma Bishop sum; DASHI original factorial,
-- signed exponential, parity, native CMP109 A/B coefficient owners.

open import Agda.Builtin.Nat using (Nat; suc)
import Real as B
import RealProperties as P
import DASHI.Foundations.BishopFiniteSeriesExtensionalityExact as Ext
import DASHI.Foundations.BishopFiniteEvenOddSeriesReindexExact as Parity
import DASHI.Foundations.BishopSignedFactorialConvolutionExact as Signed
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as E
import DASHI.Physics.YangMills.BalabanCMP102BishopShiftedCoefficientExact as Shift

-- The sum length is suc n (the EXACT count of source parity summands).
-- The final even endpoint is outside this finite sum, exactly as it is
-- in the original signedEvenRow. The odd sum has no extra endpoint.

sourceDegree : Nat → Nat
sourceDegree n = E.evenExponent (suc n)

sourceEvenTerm sourceOddTerm : Nat → Nat → B.ℝ
sourceEvenTerm n k =
  Signed.signedTerm (sourceDegree n) (E.evenExponent k)
sourceOddTerm n k =
  Signed.signedTerm (sourceDegree n) (E.oddExponent k)

-- Actual row lengths and the final retained inclusive even endpoint.
originalEvenRowFromTerms : ∀ n →
  B._≃_
    (Shift.signedEvenRow n)
    (B._+_
      (B.∑₀ (sourceEvenTerm n) (suc n))
      (Signed.signedTerm (sourceDegree n) (sourceDegree n)))
originalEvenRowFromTerms n = P.≃-refl

originalOddRowFromTerms : ∀ n →
  B._≃_ (Shift.signedOddRow n)
          (B.∑₀ (sourceOddTerm n) (suc n))
originalOddRowFromTerms n = P.≃-refl

-- One bounded same-source statement is enough to lift every even
-- summand through the original Bishop finite sum, with no new summation.
evenFiniteRowExtensional :
  (n : Nat) (expected : Nat → B.ℝ) →
  (∀ k → B._≃_ (sourceEvenTerm n k) (expected k)) →
  B._≃_
    (Shift.signedEvenRow n)
    (B._+_
      (B.∑₀ expected (suc n))
      (Signed.signedTerm (sourceDegree n) (sourceDegree n)))
evenFiniteRowExtensional n expected pointwise =
  P.≃-trans (originalEvenRowFromTerms n)
    (P.+-cong
      (Ext.finiteSumCongruent pointwise (suc n))
      P.≃-refl)

oddFiniteRowExtensional :
  (n : Nat) (expected : Nat → B.ℝ) →
  (∀ k → B._≃_ (sourceOddTerm n k) (expected k)) →
  B._≃_ (Shift.signedOddRow n)
          (B.∑₀ expected (suc n))
oddFiniteRowExtensional n expected pointwise =
  P.≃-trans (originalOddRowFromTerms n)
    (Ext.finiteSumCongruent pointwise (suc n))

-- Precise remaining source cut:
-- 1. Bounded k <= n parity-index complements for sourceDegree n.
-- 2. Identify the two endpoint products, including odd singleton n=0.
-- 3. Sum native S.aCoefficient/S.bCoefficient interiors via original
--    finite row / Cauchy reindexing and inhabit:
--       Shift.signedEvenRow n ~= Shift.evenPart n
--       Shift.signedOddRow n  ~= - Shift.oddPart n
-- The existing conditional consumer then discharges g_n=0.
-- None of these three source-specific payments is claimed here.
