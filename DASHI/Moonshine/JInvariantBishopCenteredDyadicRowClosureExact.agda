module DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact where

-- SOURCE-WRITTEN, KERNEL PENDING. Concrete C1a row endpoint on the
-- original upper-half-plane q and the original Machin exponential.
-- Pair (+k,-(k+1)) so the half-open centered interval has no lost
-- endpoints, and so the zero summand appears once.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base as N using (_⊔_; s≤s; s≤s⁻¹; z≤n) renaming (_≤_ to _≤N_; _<_ to _<N_)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (ℤ; +_; -[1+_])
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as Bounds
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Foundations.BishopBaselReciprocalSquareConvergenceExact as Basel
import DASHI.Moonshine.AbelBishopKoenigsComponentwiseCompletionExact as Completion
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Moonshine.JInvariantBishopDyadicFourierRowExact as Row
import DASHI.Moonshine.JInvariantBishopFourierRowRationalExact as Rat
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as D
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicSummandLimitExact as Leaf
import DASHI.Moonshine.JInvariantBishopCenteredDyadicTailGeometryExact as Geo
import DASHI.Moonshine.JInvariantBishopDyadicRowTailMajorantExact as Tail
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Moonshine.JInvariantBishopCenteredDyadicFoldReindexExact as Re
import DASHI.Moonshine.JInvariantBishopCenteredDyadicDominatedSumExact as Sum
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Fold
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Codec
open C using (BishopComplex; _≈C_)
open A using (_+C_; scaleC)
open Comp using (complexTrans; complexSym)
open Completion using (original-bishop-pointwise-complex-converges; realConverges; imaginaryConverges)
open Chart using (weight)
open Sum using (prefix)

pair : (ℤ → BishopComplex) → Nat → BishopComplex
pair f k = f (+ k) +C f (-[1+ k ])

pairPrefix : (ℤ → BishopComplex) → Nat → BishopComplex
pairPrefix f K = C.complex
  (prefix (λ k → C.re (pair f k)) K)
  (prefix (λ k → C.im (pair f k)) K)

intervalRead : ∀ (f : ℤ → ℝ) K →
  Fold.sum f (Re.interval K) ≃ prefix (λ k → f (+ k) + f (-[1+ k ])) K
intervalRead f zero = P.≃-refl
intervalRead f (suc K) =
  P.≃-trans (Ex.sumAppend f (Re.interval K) (+ K ∷ -[1+ K ] ∷ []))
    (P.+-cong (intervalRead f K)
      (P.+-cong P.≃-refl (P.+-identityʳ (f (-[1+ K ])))))

foldRead : ∀ n (f : ℤ → BishopComplex) →
  Chart.fold (λ w → f (Re.index {n} w)) ≈C pairPrefix f (Codec.bitCardinality n)
foldRead n f = complexTrans (Re.intervalFold n f)
  (intervalRead (λ j → C.re (f j)) (Codec.bitCardinality n) ,
   intervalRead (λ j → C.im (f j)) (Codec.bitCardinality n))

shiftReal : ∀ {f : Nat → ℝ} {v} → Seq._ConvergesTo_ f v →
  Seq._ConvergesTo_ (λ n → f (suc n)) v
shiftReal {f} {v} cv = Seq.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (Seq.shift-is-subsequence f 1) (v , cv)

unshiftReal : ∀ {f : Nat → ℝ} {v} → Seq._ConvergesTo_ (λ n → f (suc n)) v →
  Seq._ConvergesTo_ f v
unshiftReal (Seq.con* cv) = Seq.con* λ { (suc k) →
  suc (proj₁ (cv (suc k))) , λ
    { (suc zero) (s≤s ()) ; (suc (suc n)) past → proj₂ (cv (suc k)) (suc n) (s≤s⁻¹ past) } }

shiftC : ∀ {f : Nat → BishopComplex} {v} → Lim.Conv f v → Lim.Conv (λ n → f (suc n)) v
shiftC cv = original-bishop-pointwise-complex-converges
  (shiftReal (realConverges cv)) (shiftReal (imaginaryConverges cv))

previous : Nat → Nat
previous zero = zero
previous (suc k) = k

budget : ℝ → Nat → ℝ
budget c k = c * Basel.baselTerm (previous k) + c * Basel.baselTerm k

prevPrefix : ∀ n → prefix (λ k → Basel.baselTerm (previous k)) (suc n) ≃
  Basel.baselTerm zero + prefix Basel.baselTerm n
prevPrefix zero = P.+-comm R.0ℝ (Basel.baselTerm zero)
prevPrefix (suc n) =
  P.≃-trans (P.+-cong (prevPrefix n) P.≃-refl)
    (P.+-assoc (Basel.baselTerm zero) (prefix Basel.baselTerm n) (Basel.baselTerm n))

budgetRead : ∀ c n → prefix (budget c) n ≃
  c * prefix (λ k → Basel.baselTerm (previous k)) n + c * prefix Basel.baselTerm n
budgetRead c zero = let open P.ℝ-Solver in solve 1
  (λ c → Κ 0ℚᵘ ⊜ c ⊗ Κ 0ℚᵘ ⊕ c ⊗ Κ 0ℚᵘ) P.≃-refl c
budgetRead c (suc n) = P.≃-trans (P.+-cong (budgetRead c n) P.≃-refl)
  (let open P.ℝ-Solver in solve 5
    (λ c a b d e → (c ⊗ a ⊕ c ⊗ b) ⊕ (c ⊗ d ⊕ c ⊗ e)
      ⊜ c ⊗ (a ⊕ d) ⊕ c ⊗ (b ⊕ e)) P.≃-refl c
    (prefix (λ k → Basel.baselTerm (previous k)) n) (prefix Basel.baselTerm n)
    (Basel.baselTerm (previous n)) (Basel.baselTerm n))

budgetLimit : ℝ → ℝ
budgetLimit c = c * (Basel.baselTerm zero + Basel.baselLimit) + c * Basel.baselLimit

budgetConverges : ∀ c → Seq._ConvergesTo_ (prefix (budget c)) (budgetLimit c)
budgetConverges c =
  let cv = proj₂ Basel.baselSeriesConvergent
      old = Inv.addR (Power.constantConverges (Basel.baselTerm zero)) cv
      oldShift = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-symm (prevPrefix (suc n))}) (_ , old)
      both = Inv.addR (Inv.mulR (Power.constantConverges c) oldShift)
        (Inv.mulR (Power.constantConverges c) (shiftReal cv))
      shifted = Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
        (λ {(suc n) → P.≃-symm (budgetRead c (suc (suc n)))}) (_ , both)
  in unshiftReal shifted

module At (inputs : Round11.BishopCutset) (p : U.BishopUpperHalfPlanePoint) where
  module L = Leaf.At inputs
  module G = Geo.At inputs p
  module Rows = D.At inputs

  f4 f6 : Nat → ℤ → BishopComplex
  f4 n j = scaleC (weight ((+ 1 / 16) ⋆) (suc n)) (Rows.row4 (Leaf.scaledPoint p j (suc n)))
  f6 n j = scaleC (weight ((+ 1 / 64) ⋆) (suc n)) (Rows.row6 (Leaf.scaledPoint p j (suc n)))

  g4 g6 : ℤ → BishopComplex
  g4 j = Row.scale 6 (Rat.square (Rat.square (Rec.reciprocalC (L.Fixed.z p j) (L.Fixed.directionNZ p j))))
  g6 j = Row.scale 120 (Rat.cube (Rat.square (Rec.reciprocalC (L.Fixed.z p j) (L.Fixed.directionNZ p j))))

  fixed4 : ∀ k → Lim.Conv (λ n → pair (f4 n) k) (pair g4 k)
  fixed4 k = Lim.addConv (shiftC (L.Fixed.actualLimit4 p (+ k)))
    (shiftC (L.Fixed.actualLimit4 p (-[1+ k ])))

  fixed6 : ∀ k → Lim.Conv (λ n → pair (f6 n) k) (pair g6 k)
  fixed6 k = Lim.addConv (shiftC (L.Fixed.actualLimit6 p (+ k)))
    (shiftC (L.Fixed.actualLimit6 p (-[1+ k ])))

  conserved4 : ∀ n → pairPrefix (f4 n) (Codec.bitCardinality n) ≈C Rows.row4 p
  conserved4 n = complexTrans (complexSym (foldRead n (f4 n))) (L.centeredConserved4 n p)

  conserved6 : ∀ n → pairPrefix (f6 n) (Codec.bitCardinality n) ≈C Rows.row6 p
  conserved6 n = complexTrans (complexSym (foldRead n (f6 n))) (L.centeredConserved6 n p)

  cut = suc G.cutoff

  bound4 : ∀ n k → G.depth ≤N n → cut ≤N k → k <N Codec.bitCardinality n →
    Tail.Box (pair (f4 n) k) (budget G.C4 k)
  bound4 n zero nd () inside
  bound4 n (suc k) nd past inside =
    let d = NP.≤-trans nd (NP.n≤1+n n)
        i = NP.≤-trans (NP.n≤1+n G.cutoff) past
        j = NP.≤-trans i (NP.n≤1+n (suc k))
        module Pos = G.Positive n k d i inside
        module Neg = G.Negative n (suc k) d j inside
    in Tail.boxAdd Pos.four Neg.four

  bound6 : ∀ n k → G.depth ≤N n → cut ≤N k → k <N Codec.bitCardinality n →
    Tail.Box (pair (f6 n) k) (budget G.C6 k)
  bound6 n zero nd () inside
  bound6 n (suc k) nd past inside =
    let d = NP.≤-trans nd (NP.n≤1+n n)
        i = NP.≤-trans (NP.n≤1+n G.cutoff) past
        j = NP.≤-trans i (NP.n≤1+n (suc k))
        module Pos = G.Positive n k d i inside
        module Neg = G.Negative n (suc k) d j inside
    in Tail.boxAdd Pos.six Neg.six

  module FourRe = Sum.Cofinal (λ n k → C.re (pair (f4 n) k))
    (λ k → C.re (pair g4 k)) (budget G.C4) (C.re (Rows.row4 p)) (budgetLimit G.C4)
    (λ k → realConverges (fixed4 k)) (budgetConverges G.C4) G.depth cut
    (λ n k d c i → proj₁ (bound4 n k d c i)) (λ n → proj₁ (conserved4 n))
  module FourIm = Sum.Cofinal (λ n k → C.im (pair (f4 n) k))
    (λ k → C.im (pair g4 k)) (budget G.C4) (C.im (Rows.row4 p)) (budgetLimit G.C4)
    (λ k → imaginaryConverges (fixed4 k)) (budgetConverges G.C4) G.depth cut
    (λ n k d c i → proj₂ (bound4 n k d c i)) (λ n → proj₂ (conserved4 n))
  module SixRe = Sum.Cofinal (λ n k → C.re (pair (f6 n) k))
    (λ k → C.re (pair g6 k)) (budget G.C6) (C.re (Rows.row6 p)) (budgetLimit G.C6)
    (λ k → realConverges (fixed6 k)) (budgetConverges G.C6) G.depth cut
    (λ n k d c i → proj₁ (bound6 n k d c i)) (λ n → proj₁ (conserved6 n))
  module SixIm = Sum.Cofinal (λ n k → C.im (pair (f6 n) k))
    (λ k → C.im (pair g6 k)) (budget G.C6) (C.im (Rows.row6 p)) (budgetLimit G.C6)
    (λ k → imaginaryConverges (fixed6 k)) (budgetConverges G.C6) G.depth cut
    (λ n k d c i → proj₂ (bound6 n k d c i)) (λ n → proj₂ (conserved6 n))

  actualRow4 : Lim.Conv (pairPrefix g4) (Rows.row4 p)
  actualRow4 = original-bishop-pointwise-complex-converges FourRe.converges FourIm.converges

  actualRow6 : Lim.Conv (pairPrefix g6) (Rows.row6 p)
  actualRow6 = original-bishop-pointwise-complex-converges SixRe.converges SixIm.converges

  actualFourierRow4 : Lim.Conv (pairPrefix g4) (Lim.AtDisk.row (Rows.disk p) 3)
  actualFourierRow4 = Lim.limitTransport (complexSym (Rows.actualFourier4 p)) actualRow4

  actualFourierRow6 : Lim.Conv (pairPrefix g6) (Lim.AtDisk.row (Rows.disk p) 5)
  actualFourierRow6 = Lim.limitTransport (complexSym (Rows.actualFourier6 p)) actualRow6
