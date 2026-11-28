module DASHI.Moonshine.CM163BishopHecke41ReciprocalRayDomainsExact where

-- R3/R4 common actual analytic tail. SOURCE-WRITTEN, KERNEL PENDING.
-- Reuse the pinned Murray/Bishop epsilon extraction and the already
-- constructed original dyadic q reference disks. A finite sum of
-- cutoffs pays every chart, not a choice of unrelated subsequences.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Nat.Base using (_≤_; _∸_)
import Data.Nat.Properties as NP
open import Data.Fin.Base as Fin using (Fin)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Real as R
import RealProperties as P
import Sequence as Seq
open R using (∣_∣) renaming (_+_ to _+R_; _-_ to _-R_; _*_ to _*R_)
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Foundations.BishopFiniteDegreeOneGeometricBoundExact as Unit
import DASHI.Foundations.BishopSqrtTwoThirdsMachinConstantExact as MP
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Conv
import DASHI.Moonshine.CM163BishopHecke41SequentialJetExact as J
import DASHI.Moonshine.CM163BishopHecke41SecondJetCalculusExact as J2
import DASHI.Moonshine.CM163BishopHecke41ComplexExpSecondJetExact as Exp
import DASHI.Moonshine.CM163BishopHecke41AnalyticChartsExact as Chart
import DASHI.Moonshine.CM163BishopHecke41SelectedFixedChartsExact as Fixed
import DASHI.Moonshine.CM163BishopHecke41ReciprocalRayCoordinateExact as Ray
import DASHI.Moonshine.CM163BishopHecke41ActualReciprocalRayTransportExact as Tr
import DASHI.Moonshine.CM163BishopHecke41ReciprocalPhaseJetExact as PJ
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex)

record Tail (F : Nat → Set) : Set where
  field
    cutoff : Nat
    after : ∀ n → cutoff ≤ n → F n
open Tail public

-- Generic constructive strict upper bound, following
-- BishopPolynomialSuccessorFactorLimitExact's epsilon argument.
eventualLess : ∀ {f : Nat → R.ℝ} {a b} →
  Seq._ConvergesTo_ f a → R._<_ a b → Tail (λ n → R._<_ (f n) b)
eventualLess {f} {a} {b} cv lt = record
  { cutoff = suc (proj₁ receipt)
  ; after = λ n past →
      let raw = P.≤-<-trans (P.x≤∣x∣ {x = f n -R a}) (proj₂ receipt n past)
      in P.<-respʳ-≃
        (P.≃-symm (let open P.ℝ-Solver in solve 2 (λ x y → x ⊕ (y ⊖ x) ⊜ y) P.≃-refl a b))
        (P.<-respˡ-≃
          (let open P.ℝ-Solver in solve 2 (λ x y → x ⊕ (y ⊖ x) ⊜ y) P.≃-refl a (f n))
          (P.+-monoˡ-< a raw)) }
  where
  receipt = Seq.fast-ε-from-convergence (a , cv) (b -R a)
    (P.0<x⇒posx (P.x<y⇒0<y-x a b lt))

pairTail : ∀ {F G : Nat → Set} → Tail F → Tail G → Tail (λ n → F n × G n)
pairTail f g = record
  { cutoff = cutoff f + cutoff g
  ; after = λ n past →
      after f n (NP.≤-trans (NP.m≤m+n (cutoff f) (cutoff g)) past) ,
      after g n (NP.≤-trans (NP.m≤n+m (cutoff g) (cutoff f)) past) }

finiteTail : ∀ {n} {F : Fin n → Nat → Set} →
  (∀ i → Tail (F i)) → Tail (λ k → ∀ i → F i k)
finiteTail {zero} h = record { cutoff = zero ; after = λ k past () }
finiteTail {suc n} h =
  let first = h Fin.zero
      rest = finiteTail (λ i → h (Fin.suc i))
      both = pairTail first rest
  in record
    { cutoff = cutoff both
    ; after = λ k past → λ { Fin.zero → proj₁ (after both k past)
                           ; (Fin.suc i) → proj₂ (after both k past) i } }

normZero : R._≃_ (Norm.normSqC A.zeroC) R.0ℝ
normZero = let open P.ℝ-Solver in solve 0
  (Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl

module At (inputs : Round11.BishopCutset) where
  module B = PJ.At inputs zero
  module F = B.H.F.F
  module Ph = B.Ph
  module G = B.G
  open B.H.F.O using (q)

  normStrict : ∀ p → R._<_ (Norm.normSqC (q p)) R.1ℝ
  normStrict p =
    let r = F.radius p
        rp = Radius.qRadiusPositive MP.machinPiPositive (U.imaginaryPositive p)
        lt = Unit.ratioBelowOne (F.unit p)
        sqLt = P.<-respʳ-≃ (P.*-identityʳ r)
          (P.*-monoˡ-<-pos (P.0<x⇒posx rp) lt)
    in P.<-respˡ-≃ (P.≃-symm (Disk.normSquareAgreement (Ph.disk p)))
      (P.<-trans sqLt lt)

  -- Strict room, not merely the old weak centerInside inequality.
  centerStrict : ∀ p →
    let module L = B.H.Around p
    in R._<_ (Norm.normSqC (q p)) (Norm.normSqC L.D.Ref.inner)
  centerStrict p =
    let module L = B.H.Around p
        z = L.D.Ref.inner
        r = Norm.normSqC z
        eq = P.≃-trans (P.≃-symm (Phase.normCong (Ph.squareQ p)))
          (Norm.normSqMultiply z z)
    in P.<-respˡ-≃ (P.≃-symm eq)
      (P.<-respʳ-≃ (P.*-identityʳ r)
        (P.*-monoˡ-<-pos
          (P.0<x⇒posx (Rec.normSquarePositive L.D.Ref.inz))
          (normStrict L.D.Ref.innerPoint)))

  Domain : U.BishopUpperHalfPlanePoint → U.BishopUpperHalfPlanePoint → Set
  Domain p v =
    let module L = B.H.Around p
    in Exp.Inside (B.inc p v) × L.D.Ref.S.Inside (q v)

  -- First cut the exponent into its closed unit disk; derive actual
  -- q convergence there using the original exponential jet; then cut
  -- into the strictly larger dyadic analytic reference disk.
  domains : ∀ p (v : Nat → U.BishopUpperHalfPlanePoint) →
    Lim.Conv (λ n → U.tau (v n)) (U.tau p) →
    Tail (λ n → Domain p (v n))
  domains p v cv =
    let module L = B.H.Around p
        ic = B.incCV v p cv
        nc = Seq.xₙ→x∧x≃y⇒xₙ→y (Conv.normConv ic) normZero
        small = eventualLess nc (Rec.normSquarePositive Cancel.nonzeroOne)
        s = cutoff small
        vs = PJ.drop s v
        smallAt : ∀ n → Exp.Inside (B.inc p (vs n))
        smallAt n = P.<⇒≤ (after small (n + s) (NP.m≤n+m s n))
        qjet = B.H.Phase.actualPhase2 p vs (λ n → B.inc p (vs n))
          (λ n → J.recover (Ph.exponent (vs n)) (Ph.exponent p))
          smallAt (PJ.dropCV s ic)
        qc = J.continuous (PJ.dropCV s ic) (J2.first qjet)
        big = eventualLess (Conv.normConv qc) (centerStrict p)
        t = cutoff big
        sn : ∀ n → t + s ≤ n → s ≤ n
        sn n past = NP.≤-trans (NP.m≤n+m s t) past
        tn : ∀ n → t + s ≤ n → t ≤ n ∸ s
        tn n past = subst (λ k → k ≤ n ∸ s)
          (NP.m+n∸n≡m t s) (NP.∸-monoˡ-≤ s past)
    in record
      { cutoff = t + s
      ; after = λ n past →
          P.<⇒≤ (after small n (sn n past)) ,
          subst (λ k → L.D.Ref.S.Inside (q (v k)))
            (NP.m∸n+n≡m (sn n past))
            (P.<⇒≤ (after big (n ∸ s) (tn n past))) }

  centralTail = domains Fixed.p Ray.ray Ray.tauCV
  plusTail = domains Fixed.p (λ n → Tr.forward (Ray.ray n)) Tr.forwardCV
  minusTail = domains Fixed.p (λ n → Tr.reverse (Ray.ray n)) Tr.reverseCV
  chartsTail = finiteTail {n = 42}
    (λ i → domains (Chart.chartPoint i Fixed.p)
      (λ n → Chart.chartPoint i (Ray.ray n)) (PJ.chartCV i))

  allTail = pairTail (pairTail centralTail (pairTail plusTail minusTail)) chartsTail
  start : Nat
  start = cutoff allTail

  module Pj = PJ.At inputs start

  allAt : ∀ n → (Domain Fixed.p (Ray.ray (n + start)) ×
    (Domain Fixed.p (Tr.forward (Ray.ray (n + start))) ×
     Domain Fixed.p (Tr.reverse (Ray.ray (n + start))))) ×
    (∀ i → Domain (Chart.chartPoint i Fixed.p) (Chart.chartPoint i (Ray.ray (n + start))))
  allAt n = after allTail (n + start) (NP.m≤n+m start n)

  centerJet = Pj.central
    (λ n → proj₁ (proj₁ (proj₁ (allAt n))))
    (λ n → proj₂ (proj₁ (proj₁ (allAt n))))

  plusJet = Pj.plus
    (λ n → proj₁ (proj₁ (proj₂ (proj₁ (allAt n)))))
    (λ n → proj₂ (proj₁ (proj₂ (proj₁ (allAt n)))))

  minusJet = Pj.minus
    (λ n → proj₁ (proj₂ (proj₂ (proj₁ (allAt n)))))
    (λ n → proj₂ (proj₂ (proj₂ (proj₁ (allAt n)))))

  chartLimits = Pj.chartJCV
    (λ i n → proj₁ (proj₂ (allAt n) i))
    (λ i n → proj₂ (proj₂ (allAt n) i))
