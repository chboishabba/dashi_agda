module DASHI.Moonshine.CM163BishopHecke41ReducedNormFlowExact where

-- SOURCE-WRITTEN, kernel pending. Restrict the original actual complex
-- norm Euler identity to the retained sector. The factor 41 cancels
-- by positive scalar apartness, and the imaginary stream is zero by
-- the same triangular uniqueness as the real stream.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.DivMod using (_%_; _/_)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Fin.Base as Fin using (Fin)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _*_; _+_)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Cancel
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as Flow
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as Pos
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41SectorFilterExact as Filter
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; powC; scaleC)
open N
open Comp using (complexTrans; complexSym)

realC : ℝ → BishopComplex
realC x = C.complex x R.0ℝ

geoOne : ∀ z → z ≈C A.oneC → ∀ n → Filter.geometric z n ≈C realC (NR.natReal n)
geoOne z hz zero = C.≈C-refl _
geoOne z hz (suc n) =
  complexTrans (A.addCCongruent (C.≈C-refl _)
    (complexTrans (A.mulCCongruent hz (geoOne z hz n)) (L.complexMultiplyLeftIdentity _)))
    (P.≃-trans (P.+-comm R.1ℝ (NR.natReal n)) (P.≃-symm (NR.natRealSuccessor n)) ,
     P.+-identityʳ R.0ℝ)

mulAtZero : ∀ a b → (a ⊗c b) zero ≈C (a zero *C b zero)
mulAtZero a b = complexTrans (rowRead a b zero) (L.complexAddRightIdentity _)

dScale : ∀ f n →
  F.δ f (R41.stride n) ≃ NR.natReal 41 * F.δ (R41.restrict f) n
dScale f n =
  let a = NR.natReal n; p = NR.natReal 41; x = f (R41.stride n)
  in P.≃-trans
    (P.*-congʳ (P.*-congˡ (NR.natRealMul n 41)))
    (let open P.ℝ-Solver in solve 3
      (λ a p x → (Κ 1ℚᵘ ⊗ (a ⊗ p)) ⊗ x ⊜ p ⊗ ((Κ 1ℚᵘ ⊗ a) ⊗ x))
      P.≃-refl a p x)

leftReal : ∀ a b n →
  (E.lift a ⊗c b) n ≈C C.complex
    (Row.cauchyCoefficient a (C.realTerms b) n)
    (Row.cauchyCoefficient a (C.imagTerms b) n)
leftReal a b n =
  P.≃-trans (P.+-cong P.≃-refl (P.-‿cong (Ring.rowZeroLeft (C.imagTerms b) n)))
    (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl _) ,
  P.≃-trans (P.+-cong P.≃-refl (Ring.rowZeroLeft (C.realTerms b) n))
    (P.+-identityʳ _)

module At (inputs : Round11.BishopCutset) where
  module Norm = N.At inputs
  module Euler = E.At inputs
  module S = Filter.At inputs

  traceOn : ∀ f m → Euler.traceFrom (E.lift f) zero 41 (R41.stride m) ≈C
    realC (NR.natReal 41 * R41.restrict f m)
  traceOn f m = complexTrans (Euler.traceAt (E.lift f) (R41.stride m))
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (geoOne _ (S.period m) 41))
      (let open P.ℝ-Solver in solve 2
        (λ x p → x ⊗ p ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ p ⊗ x) P.≃-refl
        (R41.restrict f m) (NR.natReal 41) ,
       let open P.ℝ-Solver in solve 2
         (λ x p → x ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ p ⊜ Κ 0ℚᵘ)
         P.≃-refl (R41.restrict f m) (NR.natReal 41)))

  normFromZero : ∀ h → h zero ≃ R.1ℝ → ∀ k n →
    Norm.normFrom (E.lift h) k n zero ≈C A.oneC
  normFromZero h h0 k zero = C.≈C-refl _
  normFromZero h h0 k (suc n) =
    complexTrans (mulAtZero (Norm.factor (E.lift h) k) (Norm.normFrom (E.lift h) (suc k) n))
      (complexTrans (A.mulCCongruent
        (complexTrans (L.complexMultiplyRightIdentity (E.lift h zero)) (h0 , P.≃-refl))
        (normFromZero h h0 (suc k) n)) (L.complexMultiplyRightIdentity A.oneC))

  module For (h : G.Series) (h0 : h zero ≃ R.1ℝ) where
    module Log = E.Log h h0
    raw = Norm.norm (E.lift h)
    trace = Euler.traceFrom (E.lift Log.ell) zero 41
    driver = R41.restrict Log.ell
    reduced = R41.restrictC raw
    real : G.Series
    real = C.realTerms reduced
    imag : G.Series
    imag = C.imagTerms reduced

    driver0 : driver zero ≃ R.0ℝ
    driver0 = P.≃-trans (Row.cauchyCoefficientZero (F.δ h) Log.v)
      (P.≃-trans (P.*-congʳ (U.D0 h)) (P.*-zeroˡ _))

    zeroMode : reduced zero ≈C A.oneC
    zeroMode = normFromZero h h0 zero 41

    sectorTrace : R41.SectorC trace
    sectorTrace = Euler.traceOffSector (E.lift Log.ell)

    sectorNorm : R41.SectorC raw
    sectorNorm = Norm.offSector (E.lift h)

    reducedScaled : ∀ n →
      E.δ raw (R41.stride n) ≈C
        (E.lift (G.scale (NR.natReal 41) driver) ⊗c reduced) n
    reducedScaled n = complexTrans (Euler.actualNormFlow h h0 (R41.stride n))
      (complexTrans (R41.reduceComplex trace raw sectorTrace n)
        (N.mulCong (traceOn Log.ell) reflCs n))

    realFlow : G._≈s_ (F.δ real) (G._⊗s_ driver real)
    realFlow n = Cancel.cancelLeft (NR.natReal 41) (Pos.positiveNat 40)
      (P.≃-trans (P.≃-symm (dScale (C.realTerms raw) n))
        (P.≃-trans (proj₁ (reducedScaled n))
          (P.≃-trans (proj₁ (leftReal (G.scale (NR.natReal 41) driver) reduced n))
            (Ring.rowScaleLeft (NR.natReal 41) driver real n))))

    imagFlow : G._≈s_ (F.δ imag) (G._⊗s_ driver imag)
    imagFlow n = Cancel.cancelLeft (NR.natReal 41) (Pos.positiveNat 40)
      (P.≃-trans (P.≃-symm (dScale (C.imagTerms raw) n))
        (P.≃-trans (proj₂ (reducedScaled n))
          (P.≃-trans (proj₂ (leftReal (G.scale (NR.natReal 41) driver) reduced n))
            (Ring.rowScaleLeft (NR.natReal 41) driver imag n))))

    imagZero : G._≈s_ imag H.zeroSeries
    imagZero = D.solveUnique driver imag H.zeroSeries driver0 imagFlow
      (G.transS Flow.dZero (G.symS (H.zeroRow driver)))
      (proj₂ zeroMode)

    -- Any real recurrence solution with the same initial coefficient
    -- is the actual complex cyclic norm after exact degree restriction.
    uniqueReal : ∀ f → f zero ≃ R.1ℝ →
      G._≈s_ (F.δ f) (G._⊗s_ driver f) → reduced ≈cs E.lift f
    uniqueReal f f0 flow n =
      D.solveUnique driver real f driver0 realFlow flow
        (P.≃-trans (proj₁ zeroMode) (P.≃-symm f0)) n ,
      imagZero n

    reconstruct : raw ≈cs R41.expandC (E.lift real)
    reconstruct = transCs (symCs (R41.reconstruct raw sectorNorm))
      (expandCong (λ n → P.≃-refl , imagZero n))
      where
      expandCong : ∀ {a b} → a ≈cs b → R41.expandC a ≈cs R41.expandC b
      expandCong {a} {b} h n with n % 41 NP.≟ zero
      ... | yes _ = h (n / 41)
      ... | no _ = C.≈C-refl _

  module Diagonal = For Actual.hDiag Actual.hDiag0
  module Slice = For Actual.hSlice Actual.hSlice0
