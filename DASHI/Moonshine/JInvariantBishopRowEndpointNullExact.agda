module DASHI.Moonshine.JInvariantBishopRowEndpointNullExact where

-- SOURCE-WRITTEN, kernel pending. A single exposed vertical endpoint
-- is dominated by the ORIGINAL absolute shell, not by the value of a
-- signed total. This supplies the centered-to-symmetric row limit.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; _⊔_)
import Data.Nat.Properties as NP
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
open import Data.Bool.Base using (T; tt; not)
open import Data.Bool.Properties using (T-∧)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_; allFin)
open import Data.List.Membership.Propositional using (_∈_)
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.All as All
import Data.List.Relation.Unary.AllPairs.Core as AP
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Real as R
open R using (ℝ; _≃_; _-_; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Physics.Closure.NSTriadKNPhysicalRetainedSector as Cut
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantPuncturedLatticeSquareShellExact as S
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSymmetricRowChartExact as Chart
import DASHI.Moonshine.JInvariantBishopCenteredDyadicRowClosureExact as Close
import DASHI.Moonshine.JInvariantBishopFourierRowLimitExact as Lim
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Analysis.BishopMachinZetaSequentialContinuityReducerExact as Eps
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ)

notTruth : ∀ b → (T b → ⊥) → T (not b)
notTruth true h = ⊥-elim (h tt)
notTruth false h = tt

endpointShell : ∀ j n → Z.∣ j ∣ ≤ suc n →
  T (S.onSuccessorSquareShell? n (L.lattice-point j (+ suc n)))
endpointShell j n h = Equivalence.from T-∧
  (Equivalence.from T-∧ (Chart.magnitudeCutoff (suc n) j h ,
    Chart.magnitudeCutoff (suc n) (+ suc n) NP.≤-refl) ,
   notTruth _ λ inside → NP.1+n≰n
     (Chart.cutoffMagnitude n (+ suc n) (proj₂ (Equivalence.to T-∧ inside))))

-- Positive absolute shell sum contains the endpoint exactly once.
pointBelowShell : ∀ f → Re.PointRespect f → ∀ n p →
  T (S.onSuccessorSquareShell? n p) →
  R._≤_ ∣ Ex.raw f p ∣ (F.shellAbsolute n f)
pointBelowShell f respect n p hp =
  let a = λ i → ∣ f i ∣
      ar : Re.PointRespect a
      ar i j h = P.∣-∣-cong (respect i j h)
      ls = S.successorSquareShell n
      inc : ∀ {q} → q ∈ (p ∷ []) →
        q ∈ ls
      inc (Any.here refl) = Re.shellMember n p hp
      inc (Any.there ())
      mono = Ex.subsetMono (λ q → ∣ Ex.raw f q ∣)
        (λ q → P.nonNeg∣x∣ (Ex.raw f q))
        (AP._∷_ All.[] AP.[]) (S.successorSquareShellUnique n) inc
      read = P.≃-trans (Re.sumCong (λ q → ∣ Ex.raw f q ∣) (Ex.raw a) ls
        (λ q → P.≃-symm (Ex.rawAbs f q))) (P.≃-symm (Ex.shellRead n a ar))
  in P.≤-respˡ-≃ (P.+-identityʳ ∣ Ex.raw f p ∣) (P.≤-respʳ-≃ read mono)

-- Eventual domination, using the actual positive error precision.
-- A finite number of exceptional early endpoints is irrelevant.
eventualNull : ∀ (f b : Nat → ℝ) cut →
  Seq._ConvergesTo_ b R.0ℝ →
  (∀ n → cut ≤ n → R._≤_ ∣ f n ∣ (b n)) →
  Seq._ConvergesTo_ f R.0ℝ
eventualNull f b cut conv bound = Seq.con* λ { (suc k) →
  let eps = R._⋆ (+ 1 / suc k)
      mod = Seq.fast-ε-from-convergence (R.0ℝ , conv) eps (Eps.reciprocalNatPositive k)
      stop = cut ⊔ proj₁ mod
  in stop , λ n past →
    let after = NP.≤-trans (NP.n≤1+n stop) past
        hc = NP.≤-trans (NP.m≤m⊔n cut (proj₁ mod)) after
        hm = NP.≤-trans (NP.m≤n⊔m cut (proj₁ mod)) after
        hb = P.<⇒≤ (proj₂ mod n hm)
        bnd = P.≤-trans (bound n hc)
          (P.≤-trans P.x≤∣x∣ (P.≤-respˡ-≃ (P.∣-∣-cong
            (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (b n))) hb))
    in P.≤-respˡ-≃ (P.≃-symm (P.∣-∣-cong
      (let open P.ℝ-Solver in solve 1 (λ x → x ⊖ Κ 0ℚᵘ ⊜ x) P.≃-refl (f n)))) bnd }

module At (f : K.NonzeroLatticePoint → ℝ) (respect : Re.PointRespect f)
  (a : ℝ) (absolute : Seq._ConvergesTo_ (Seq.SeriesOf (λ n → F.shellAbsolute n f)) a)
  where
  endpoint : ℤ → Nat → ℝ
  endpoint j n = Ex.raw f (L.lattice-point j (+ n))

  successorNull : ∀ j → Seq._ConvergesTo_ (λ n → endpoint j (suc n)) R.0ℝ
  successorNull j = eventualNull (λ n → endpoint j (suc n)) (λ n → F.shellAbsolute n f) (Z.∣ j ∣)
    (Lim.seriesTermNull _ a absolute)
    (λ n h → pointBelowShell f respect n (L.lattice-point j (+ suc n))
      (endpointShell j n (NP.≤-step h)))

  endpointNull : ∀ j → Seq._ConvergesTo_ (endpoint j) R.0ℝ
  endpointNull j = Close.unshiftReal (successorNull j)

  -- Original centered row plus its vanishing endpoint, then permutation
  -- to the exact decoder used by RectangleRowLimitAttachment.
  symmetricLimit : ∀ j v →
    Seq._ConvergesTo_ (Seq.SeriesOf (λ k → R._+_
      (Ex.raw f (L.lattice-point j (+ k)))
      (Ex.raw f (L.lattice-point j (Z.-[1+ k ]))))) v →
    Seq._ConvergesTo_ (λ n → Re.sum (λ i → Ex.raw f
      (L.lattice-point j (Cube.decodeCoordinate n i))) (allFin (Cube.coordinateCodeBound n))) v
  symmetricLimit j v centered =
    let h = λ z → Ex.raw f (L.lattice-point j z)
        add = Inv.addR centered (endpointNull j)
        converted = Seq.xₙ→x∧x≃y⇒xₙ→y add (P.+-identityʳ v)
    in Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc n) → P.≃-symm (P.≃-trans (Chart.codeSum h (suc n))
        (Chart.symmetricPairRead h (suc n)))}) (v , converted)
