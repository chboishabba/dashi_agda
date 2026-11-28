module DASHI.Moonshine.CM163BishopHecke41OriginalRayClosureExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- Close the local geometry using the common actual analytic tail.
-- The exact remaining coefficient weld is the two Euler moments of
-- the original normalized J/q, not three branch-specific jets.
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (+_; -_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)
import Data.Nat.Properties as NP
import Real as R
import RealProperties as P
open R using (_*_; _⋆)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNonzeroFromComponentExact as NZ
import DASHI.Analysis.BishopMachinEventualHalfPlaneExact as Above
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopCM163ReciprocalGeometryExact as Geo
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as CM
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Disk
import DASHI.Moonshine.JInvariantBishopCM163QuotientJetExact as QJ
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Literal
import DASHI.Moonshine.JInvariantBishopCM163LiteralTerminalExact as Terminal
import DASHI.Moonshine.CM163BishopHecke41ActualCrossExact as Cross
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41SelectedRootWeldExact as Root
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Matrix
import DASHI.Moonshine.CM163BishopHecke41ReciprocalRayCoordinateExact as Ray
import DASHI.Moonshine.CM163BishopHecke41ReciprocalPhaseJetExact as PJ
import DASHI.Moonshine.CM163BishopHecke41ReciprocalRayDomainsExact as Domains
import DASHI.Moonshine.CM163BishopHecke41SelectedEulerReadbackExact as Euler
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHecke41ComplexPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41PolynomialEvaluationExact as Poly
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as Period
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open A using (_-C_; _*C_; _+C_)
open Comp using (complexTrans; complexSym)
open Poly using (realC)

ellR : R.ℝ
ellR = (((- (+ 2)) / 1) ⋆) * CM.p

ellRead : PJ.ell ≈C realC ellR
ellRead =
  (let open P.ℝ-Solver in solve 2 (λ p r →
    Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊖ (Κ (+ 2 / 1) ⊗ p) ⊗
      ((Κ (+ 1 / 2) ⊗ r) ⊕ (Κ (+ 1 / 2) ⊗ r))
    ⊜ Κ ((- (+ 2)) / 1) ⊗ (p ⊗ r))
    P.≃-refl Phase.pi N.r) ,
  (let open P.ℝ-Solver in solve 2 (λ p r →
    Κ 0ℚᵘ ⊗ ((Κ (+ 1 / 2) ⊗ r) ⊕ (Κ (+ 1 / 2) ⊗ r)) ⊕
      (Κ (+ 2 / 1) ⊗ p) ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ)
    P.≃-refl Phase.pi N.r)

halfB : R.ℝ
halfB = ((+ 1 / 2) ⋆) * QJ.b

module At (inputs : Round11.BishopCutset) where
  module D = Domains.At inputs
  module Pj = D.Pj
  module M = Matrix.At inputs
  module H = M.H

  -- The same evaluated quotient moments, with Taylor-2 = Euler^2/2.
  -- This explicitly isolates the remaining source-series readback.
  EulerRead : Set
  EulerRead = (Pj.Base.euler1 ≈C realC QJ.a)
  SecondEulerRead : Set
  SecondEulerRead = (Pj.Base.eulerTaylor2 ≈C realC halfB)

  aRead : EulerRead → Pj.a0 ≈C realC (Disk.A CM.p QJ.a)
  aRead h = complexTrans (A.mulCCongruent ellRead h) (Root.realMul ellR QJ.a)

  bRead : EulerRead → SecondEulerRead → Pj.b0 ≈C realC (Disk.diskB CM.p QJ.a QJ.b)
  bRead h k =
    let mulReal = complexTrans (A.mulCCongruent ellRead
          (complexTrans (A.mulCCongruent ellRead k) (Root.realMul ellR halfB)))
          (Root.realMul ellR (ellR * halfB))
        scalar = let open P.ℝ-Solver in solve 3 (λ p a b →
          (Κ ((- (+ 2)) / 1) ⊗ p ⊗ a) ⊕
          ((Κ ((- (+ 2)) / 1) ⊗ p) ⊗ ((Κ ((- (+ 2)) / 1) ⊗ p) ⊗ (Κ (+ 1 / 2) ⊗ b)))
          ⊜ (Κ ((- (+ 2)) / 1) ⊗ p ⊗ a) ⊕ Κ (+ 2 / 1) ⊗ (p ⊗ p) ⊗ b)
          P.≃-refl CM.p QJ.a QJ.b
    in complexTrans (A.addCCongruent (aRead h) mulReal)
      (complexTrans (Root.realAdd (Disk.A CM.p QJ.a) (ellR * (ellR * halfB)))
        (scalar , P.≃-refl))

  module Direct (sym : M.TwoPointSymmetry)
    (hd : ∀ p → H.R.d p ≈C A.zeroC)
    (hs : ∀ p → H.R.s p ≈C A.zeroC)
    (h1 : EulerRead) (h2 : SecondEulerRead) where

    module End = M.ImageClosure sym hd hs
    a = End.RY.a
    b = End.RY.b

    rootRead : H.G.j Fixed.p ≈C Shift.K
    rootRead = M.selectedK End.root

    X Xp Xm : Nat → BishopComplex
    X = J.quotient (J2.first D.centerJet)
    Xp = J.quotient (J2.first D.plusJet)
    Xm = J.quotient (J2.first D.minusJet)

    hx : ∀ n → H.x (Pj.point n) ≈C (Pj.W n *C X n)
    hx n = complexTrans (A.subCCongruent (C.≈C-refl _) (complexSym rootRead))
      (J.factor (J2.first D.centerJet) n)

    hp : ∀ n → H.xp (Pj.point n) ≈C (Pj.W n *C Xp n)
    hp n = complexTrans (A.subCCongruent (C.≈C-refl _) (complexSym rootRead))
      (J.factor (J2.first D.plusJet) n)

    hm : ∀ n → H.xm (Pj.point n) ≈C (Pj.W n *C Xm n)
    hm n = complexTrans (A.subCCongruent (C.≈C-refl _) (complexSym rootRead))
      (J.factor (J2.first D.minusJet) n)

    jx : J.Jet Pj.W X (realC a) (realC b)
    jx = J.congJet (λ _ → C.≈C-refl _) (aRead h1) (bRead h1 h2) (J2.second D.centerJet)

    jp : J.Jet Pj.W Xp (Geo.p0 a) (Geo.p1 b)
    jp = J.congJet (λ _ → C.≈C-refl _)
      (A.mulCCongruent (C.≈C-refl _) (aRead h1))
      (A.mulCCongruent (C.≈C-refl _) (bRead h1 h2)) (J2.second D.plusJet)

    jm : J.Jet Pj.W Xm (Geo.m0 a) (Geo.m1 b)
    jm = J.congJet (λ _ → C.≈C-refl _)
      (A.mulCCongruent (C.≈C-refl _) (aRead h1))
      (A.mulCCongruent (C.≈C-refl _) (bRead h1 h2)) (J2.second D.minusJet)

    xCV : Lim.Conv (λ n → H.x (Pj.point n)) A.zeroC
    xCV = Lim.convTransport (λ n → complexSym (hx n))
      (Lim.limitTransport (L.complexMultiplyLeftZero Pj.a0)
        (Conv.mulConv Pj.wCV (J.limit (J2.first D.centerJet))))

    wNZ : ∀ n → Rec.BishopComplexNonzero (Pj.W n)
    wNZ n = Ray.wNZ (n + D.start)

    -- No arbitrary j-image apartness assumption: the signed first
    -- coefficient is apart by the already-owned selected Euler law.
    aNZ : Rec.BishopComplexNonzero Pj.a0
    aNZ = Phase.guardCong (complexSym (aRead h1))
      (NZ.complexNonzeroFromRealApart (Literal.diskApart QJ.a (QJ.first End.root)))

    apart = Above.bishopConvergenceEventuallyAbove
      (Conv.normConv (J.limit (J2.first D.centerJet))) (Rec.normSquarePositive aNZ)

    test = PJ.drop (proj₁ apart) Pj.point

    testNZ : ∀ n → Rec.BishopComplexNonzero (H.x (test n))
    testNZ n =
      let k = n + proj₁ apart
          xnz : Rec.BishopComplexNonzero (X k)
          xnz = record { Rec.normSquarePositive = proj₂ apart k (NP.m≤n+m (proj₁ apart) n) }
      in Phase.guardCong (complexSym (hx k)) (Cancel.nonzeroMul (wNZ k) xnz)

    testCV : Lim.Conv (λ n → H.x (test n)) A.zeroC
    testCV = PJ.dropCV (proj₁ apart) xCV

    originalRay : Terminal.OriginalRayResidual
    originalRay = End.ray test testNZ testCV Pj.W Pj.point X Xp Xm
      Pj.wCV wNZ hx hp hm jx jp jm D.chartLimits xCV

    allRaw : (k : Nat) → Raw.RawCross k
    allRaw = End.allRaw originalRay

    period : Period.NativePeriod
    period = Terminal.periodFromDiagonalAndRay (M.SR.diagonalFromResidual (hd Fixed.p)) originalRay


  -- The two source Euler equalities are constructed, not premises of
  -- the canonical direct endpoint. Keep Direct as a diagnostic seam.
  module SourceEuler = Euler.At inputs

  originalEulerRead : EulerRead
  originalEulerRead = SourceEuler.eulerRead

  originalSecondEulerRead : SecondEulerRead
  originalSecondEulerRead = SourceEuler.secondEulerRead

  module Original (sym : M.TwoPointSymmetry)
    (hd : ∀ p → H.R.d p ≈C A.zeroC)
    (hs : ∀ p → H.R.s p ≈C A.zeroC) where
    module Closed = Direct sym hd hs originalEulerRead originalSecondEulerRead
    open Closed public using (originalRay; allRaw; period)
