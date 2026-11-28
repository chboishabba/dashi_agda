module DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact where

-- Source-written, kernel pending. The selected original CM quotient is
-- the actual upper-half-plane q-series quotient. Both reciprocal charts
-- give the same j, using the original CM quadratic and existing guard.
-- The cleared diagonal requires no guard for any other chart.
open import Data.Fin as Fin
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as Laws
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163OriginalPhaseExact as Phase
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as J
import DASHI.Moonshine.JInvariantBishopNativeProofRelevantKleinExact as Klein
import DASHI.Moonshine.JInvariantBishopDiskSetoidTransportExact as Cong
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as G
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; scaleC)
open Comp using (complexTrans; complexSym)

p : U.BishopUpperHalfPlanePoint
p = U.bishop-upper-half-plane-point CM.tau CM.imagPositive

scaleRight : ∀ h a b → (a *C scaleC h b) ≈C scaleC h (a *C b)
scaleRight h (C.complex a b) (C.complex c d) =
  (let open P.ℝ-Solver in solve 5 (λ h a b c d →
    a ⊗ (h ⊗ c) ⊖ b ⊗ (h ⊗ d) ⊜ h ⊗ (a ⊗ c ⊖ b ⊗ d)) P.≃-refl h a b c d) ,
  (let open P.ℝ-Solver in solve 5 (λ h a b c d →
    a ⊗ (h ⊗ d) ⊕ b ⊗ (h ⊗ c) ⊜ h ⊗ (a ⊗ d ⊕ b ⊗ c)) P.≃-refl h a b c d)

tRead : U.tau (G.actT p) ≈C Geo.fDen CM.tau
tRead = P.≃-refl , P.≃-symm (P.+-identityʳ (C.im CM.tau))

finite1Read : U.tau (Chart.finitePoint 1 p) ≈C scaleC Chart.inv41 (Geo.fDen CM.tau)
finite1Read = P.≃-refl , P.*-congˡ (P.≃-symm (P.+-identityʳ (C.im CM.tau)))

finite0Read : U.tau (Chart.finitePoint 0 p) ≈C scaleC Chart.inv41 CM.tau
finite0Read = P.*-congˡ (P.+-identityʳ (C.re CM.tau)) , P.≃-refl

scaleMinus41 : scaleC Chart.inv41 (Geo.fNum CM.tau) ≈C G.minusOneC
scaleMinus41 =
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1 / 41) ⊗ Κ (- (+ 41) / 1) ⊜ ⊝ Κ 1ℚᵘ) P.≃-refl) ,
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 1 / 41) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl)

forwardProduct : (CM.tau *C U.tau (Chart.finitePoint 1 p)) ≈C G.minusOneC
forwardProduct = complexTrans (A.mulCCongruent (C.≈C-refl _) finite1Read)
  (complexTrans (scaleRight Chart.inv41 CM.tau (Geo.fDen CM.tau))
    (complexTrans (A.scaleCCongruent (complexSym Geo.forwardFixed) Chart.inv41) scaleMinus41))

reverseProduct : (U.tau (G.actT p) *C U.tau (Chart.finitePoint 0 p)) ≈C G.minusOneC
reverseProduct = complexTrans (A.mulCCongruent (C.≈C-refl _) finite0Read)
  (complexTrans (scaleRight Chart.inv41 _ CM.tau)
    (complexTrans (A.scaleCCongruent (Laws.complexMultiplyCommutative _ CM.tau) Chart.inv41)
      (complexTrans (A.scaleCCongruent (A.mulCCongruent (C.≈C-refl _) tRead) Chart.inv41)
        (complexTrans (A.scaleCCongruent (complexSym Geo.forwardFixed) Chart.inv41) scaleMinus41))))

-- These are actual parameter equalities, not just a polynomial root.
fixed1 : U.tau (Chart.chartPoint (Fin.suc Fin.zero) p) ≈C U.tau (G.actS p)
fixed1 = J.cancelLeft CM.tau _ _ (G.tauNZ p) (complexTrans forwardProduct (complexSym (G.tauTimesS p)))

fixed0 : U.tau (Chart.chartPoint Fin.zero p) ≈C U.tau (G.actS (G.actT p))
fixed0 = J.cancelLeft (U.tau (G.actT p)) _ _ (G.tauNZ (G.actT p))
  (complexTrans reverseProduct (complexSym (G.tauTimesS (G.actT p))))

module At (inputs : Round11.BishopCutset) where
  module K = J.At inputs
  module Ph = D.At inputs
  module E = Cong.At inputs
  module H = Prod.At inputs

  qRead : Ph.q p ≈C CM.q
  qRead = complexTrans (complexSym (Ph.actualQ p)) (Phase.AtOriginal.qFromOriginalAtans inputs)

  module Same = Cong.Disks (Ph.disk p) CM.input qRead

  nRead : K.N p ≈C Klein.cube CM.Selected.Actual.E4
  nRead = J.cubeCong Same.e4

  dRead : K.D p ≈C CM.Selected.Actual.Delta
  dRead = J.deltaCong Same.e4 Same.e6

  guard : K.Guard p
  guard = D.guardCong (complexSym dRead) Guard.Root.nz

  selectedJ : K.j p guard ≈C CM.Selected.Actual.jFromNegativeDelta Guard.negativeDelta
  selectedJ = J.quotCong nRead dRead guard Guard.Root.nz

  realSelectedJ : R._≃_ (C.re (K.j p guard)) Guard.Root.j
  realSelectedJ = proj₁ selectedJ

  guard1 : K.Guard (Chart.chartPoint (Fin.suc Fin.zero) p)
  guard1 = E.guardCong _ _ (complexSym fixed1) (K.guardS p guard)

  guard0 : K.Guard (Chart.chartPoint Fin.zero p)
  guard0 = E.guardCong _ _ (complexSym fixed0) (K.guardS (G.actT p) (K.guardT p guard))

  j1 : K.j (Chart.chartPoint (Fin.suc Fin.zero) p) guard1 ≈C K.j p guard
  j1 = complexTrans (E.jCong _ _ fixed1 guard1 (K.guardS p guard))
    (K.jS p guard (K.guardS p guard))

  j0 : K.j (Chart.chartPoint Fin.zero p) guard0 ≈C K.j p guard
  j0 = complexTrans (E.jCong _ _ fixed0 guard0 (K.guardS (G.actT p) (K.guardT p guard)))
    (complexTrans (K.jS (G.actT p) (K.guardT p guard) (K.guardS (G.actT p) (K.guardT p guard)))
      (K.jT p guard (K.guardT p guard)))

  factor0 : H.factor p Fin.zero ≈C A.zeroC
  factor0 = H.fixedFactor p Fin.zero guard guard0 j0

  factor1 : H.factor p (Fin.suc Fin.zero) ≈C A.zeroC
  factor1 = H.fixedFactor p (Fin.suc Fin.zero) guard guard1 j1

  clearedDiagonalZero : H.clearedDiagonal p ≈C A.zeroC
  clearedDiagonalZero = H.fixedClearedDiagonal p Fin.zero guard guard0 j0

  -- The quotient product zero consumes only the still-unpaid global
  -- chart guards, not any modular polynomial identity or root assertion.
  quotientDiagonalZero : (all : H.AllGuards p) → H.diagonal p guard all ≈C A.zeroC
  quotientDiagonalZero all = H.fixedDiagonal p Fin.zero guard all
    (complexTrans (E.jCong _ _ (C.≈C-refl _) (all Fin.zero) guard0) j0)
