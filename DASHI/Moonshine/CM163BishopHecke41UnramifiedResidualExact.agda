module DASHI.Moonshine.CM163BishopHecke41UnramifiedResidualExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Descent of the original all-degree convergent residual, not just
-- the integer prefix.  The ordinary q-series has zero constant
-- term after the exact pole removal.  No inverse exponential needed.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
open import Data.Nat.Base using (_≤_; s≤s)
import Data.Nat.Properties as NP
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopThetaCauchyProductExact as CP
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact as Ref
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Coeff
import DASHI.Moonshine.CM163BishopHecke41CuspResidualExact as Residual
import DASHI.Moonshine.CM163BishopHecke41CuspTailFactorExact as Tail
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_-C_; _*C_; powC)
open Comp using (complexTrans; complexSym)
open R41 using (stride; restrict; restrictC; Sector; SectorC)
open N using (twist; _≈cs_)

-- Converse of the existing sparseConverges.  Keep every compressed
-- cutoff, rather than appeal to convergence of a guessed subsequence.
contractConv : ∀ f → Sector f → ∀ v →
  Seq._ConvergesTo_ (Seq.SeriesOf f) v →
  Seq._ConvergesTo_ (Seq.SeriesOf (restrict f)) v
contractConv f hf v (Seq.con* cv) = Seq.con* λ { (suc k) →
  proj₁ (cv (suc k)) , λ { (suc n) (s≤s past) →
    P.≤-respˡ-≃
      (P.∣-∣-cong (P.+-cong (R41.prefixStride f hf n) P.≃-refl))
      (proj₂ (cv (suc k)) (suc (stride n))
        (s≤s (NP.≤-trans past (NP.m≤m*n n 41)))) } }

contractAbs : ∀ f → Sector f →
  Seq.SeriesOf_ConvergesAbsolutely f →
  Seq.SeriesOf_ConvergesAbsolutely (restrict f)
contractAbs f hf ab =
  proj₁ ab , contractConv (λ n → R.∣ f n ∣) (Eval.absSector f hf) (proj₁ ab) (proj₂ ab)

contractEval : ∀ {t q f} → powC t 41 ≈C q → SectorC f →
  Eval.Eval t f → Eval.Eval q (restrictC f)
contractEval {t} {q} {f} tq sector ev =
  let terms = twist t f
      zeros : SectorC terms
      zeros n hn = complexTrans (A.mulCCongruent (sector n hn) (C.≈C-refl _))
        (L.complexMultiplyLeftZero _)
      reS : Sector (C.realTerms terms)
      reS n hn = proj₁ (zeros n hn)
      imS : Sector (C.imagTerms terms)
      imS n hn = proj₂ (zeros n hn)
      eq : ∀ n → restrictC terms n ≈C twist q (restrictC f) n
      eq n = A.mulCCongruent (C.≈C-refl _)
        (complexTrans (complexSym (Ram.powPow t 41 n)) (A.powCCongruent tq n))
      ab = C.componentwise-absolute-series-convergent
        (contractAbs (C.realTerms terms) reS (C.realAbsolute (Eval.absolute ev)))
        (contractAbs (C.imagTerms terms) imS (C.imagAbsolute (Eval.absolute ev)))
      cv = C.complex-series-converges-to
        (contractConv (C.realTerms terms) reS (C.re (Eval.value ev)) (C.realConverges (Eval.converges ev)))
        (contractConv (C.imagTerms terms) imS (C.im (Eval.value ev)) (C.imagConverges (Eval.converges ev)))
  in record
    { Eval.value = Eval.value ev
    ; Eval.absolute = CP.complexAbsTransport eq ab
    ; Eval.converges = CP.complexLimitTransport eq cv }

subSector : ∀ a b → SectorC a → SectorC b → SectorC (λ n → a n -C b n)
subSector a b ha hb n hn = complexTrans (A.subCCongruent (ha n hn) (hb n hn)) (J.sameSub A.zeroC)

strideMono : ∀ {n d} → n ≤ d → stride n ≤ stride d
strideMono h = NP.*-monoˡ-≤ 41 h

-- Generic actual residual with a zero coefficient prefix through d.
-- Dropping d (not d+1) leaves the zero constant term visible.  The
-- evaluation is an ordinary q power series for the ORIGINAL residual.
record ZeroConstantSeries (q : BishopComplex) (v : BishopComplex) : Set where
  field
    coefficients : N.SeriesC
    zeroConstant : coefficients zero ≈C A.zeroC
    evaluated : Eval.Eval q coefficients
    actual : v ≈C Eval.value evaluated

module Remove (d : Nat) (q v : BishopComplex)
  (nz : Rec.BishopComplexNonzero q) (f : N.SeriesC)
  (ev : Eval.Eval q f)
  (clear : (powC q (suc d) *C v) ≈C Eval.value ev)
  (zeros : ∀ n → n ≤ suc d → f n ≈C A.zeroC) where
  coefficients = Tail.drop (suc d) f
  readout = Tail.tailRead nz (suc d) ev
  dropRead : ∀ k (g : N.SeriesC) → Tail.drop k g zero ≡ g k
  dropRead zero g = refl
  dropRead (suc k) g = dropRead k (λ n → g (suc n))

  constantZero : coefficients zero ≈C A.zeroC
  constantZero rewrite dropRead (suc d) f = zeros (suc d) NP.≤-refl

  equality : v ≈C Eval.value readout
  equality = Cancel.cancelLeft (powC q (suc d)) v (Eval.value readout)
    (Cancel.nonzeroPower nz (suc d))
    (complexTrans clear (Tail.factor nz d ev (λ n hn → zeros n (NP.≤-step hn))))

  result : ZeroConstantSeries q v
  result = record { coefficients = coefficients ; zeroConstant = constantZero
                  ; evaluated = readout ; actual = equality }

module At (inputs : Round11.BishopCutset) where
  module R0 = Residual.At inputs
  module O = R0.R.O
  q = R0.V.A0.q

  dSector : SectorC O.diagonalResidual
  dSector = subSector O.diagonalNormalized (E.lift Coeff.diagColumn)
    (Ref.complexSectorProduct (E.lift Coeff.gDiag) O.diagNorm
      (Ref.liftSector Coeff.gDiag Ref.gDiagSector) O.diagOffSector)
    (Ref.liftSector Coeff.diagColumn (Ref.columnSector Packet.diagonal))

  sSector : SectorC O.sliceResidual
  sSector = subSector O.sliceNormalized (E.lift Coeff.sliceColumn)
    (Ref.complexSectorProduct (E.lift Coeff.gSlice) O.sliceNorm
      (Ref.liftSector Coeff.gSlice Ref.gSliceSector) O.sliceOffSector)
    (Ref.liftSector Coeff.sliceColumn (Ref.columnSector Packet.slice))

  dEval p = contractEval (R0.V.Rm.tPower p) dSector (R0.dEval p)
  sEval p = contractEval (R0.V.Rm.tPower p) sSector (R0.sEval p)

  powerRead : ∀ p n → powC (q p) n ≈C powC (R0.t p) (stride n)
  powerRead p n = complexTrans (A.powCCongruent (complexSym (R0.V.Rm.tPower p)) n)
    (Ram.powPow (R0.t p) 41 n)

  diagonal (hu : R0.R.W.UnitGate) (hd : R0.R.W.DiagonalGate) p =
    Remove.result 81 (q p) (R0.d p) (R0.G.qNonzero p)
      (restrictC O.diagonalResidual) (dEval p)
      (complexTrans (A.mulCCongruent (powerRead p 82) (C.≈C-refl _)) (R0.dClear p))
      (λ n hn → R0.R.diagonalZero hu hd (stride n) (strideMono hn))

  slice (hu : R0.R.W.UnitGate) (hs : R0.R.W.SliceGate) p =
    Remove.result 41 (q p) (R0.s p) (R0.G.qNonzero p)
      (restrictC O.sliceResidual) (sEval p)
      (complexTrans (A.mulCCongruent (powerRead p 42) (C.≈C-refl _)) (R0.sClear p))
      (λ n hn → R0.R.sliceZero hu hs (stride n) (strideMono hn))
