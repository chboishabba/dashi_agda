module DASHI.Analysis.BishopOriginalEtaPairBlockTelescopingExact where

------------------------------------------------------------------------
-- ACTUAL MURRAY/BISHOP ORIGINAL ETA: ALL-CUTOFF SHIFTED PAIR TAIL.
--
-- The original Round11 even/odd eta block is
--   a(2j) - a(2j+1)
-- on BishopOriginalDirichletEtaFinitePairingExact.originalEtaBlock.
-- This source theorem REUSES that very block, that very finite
-- prefix and the literal original selected nat-log/complex exp term.
--
-- A genuinely constructive finite identity on the original Bishop
-- real setoid, proved in both complex coordinates:
--
--   eta_(n+m) = eta_n + sum_{j=0}^{m-1}
--                          [a(2(n+j)) - a(2(n+j)+1)].
--
-- This is the exact shifted-pair/telescoping entry point for the
-- Abel uniform tail (BishopOriginalEtaAbelUniformTail20261114.md).
-- The difficult analytic step remains an original source estimate
--   |a(j)-a(j+1)| <= (|s|/sigma) Delta j^{-sigma},
-- plus the actual Bishop log equality, complex differentiation,
-- fundamental theorem, norms and uniform Cauchy modulus.
--
-- This module has no new postulate, no synthetic complex carrier and
-- NO claim of eta compact-uniform convergence or RH. Pinned Agda
-- kernel/type checking of this source-written term still required.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
import Data.Nat.Properties as NatP
open import Data.Nat.Base using (_≤_; _∸_; NonZero)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Relation.Binary.PropositionalEquality as Eq
import Sequence as Seq

open import Data.Rational.Unnormalised using (0ℚᵘ)
import Real as R
import RealProperties as RP

import DASHI.Analysis.RiemannBishopComplexAnalyticCarrierExact as BC
import DASHI.Analysis.BishopOriginalDirichletEtaFinitePairingExact as Eta
import DASHI.Analysis.BishopRiemannDirichletExponentialTermExact as Terms
import DASHI.Analysis.BishopOriginalNegativeLogTerminalFromMeshExact as Log
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as ExpCong
import DASHI.Foundations.BishopExponentialPositiveOrderExact as Pos
import DASHI.Foundations.BishopExponentialCauchyProductExact as ExpProduct
import DASHI.Foundations.BishopNegativeExponentialGlobalUnitIntervalExact as Neg
import DASHI.Analysis.BishopGeometricMajorantSeriesConvergenceExact as Geo

import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11

-- The original eta blocks are sums in the original Bishop complex
-- carrier. No change in sign convention or zero/one-based indexing.
originalShiftedEtaPairs :
  (Nat → BC.BishopComplex) → Nat → Nat → BC.BishopComplex
originalShiftedEtaPairs term n zero = BC.zeroC
originalShiftedEtaPairs term n (suc m) =
  BC._+C_
    (originalShiftedEtaPairs term n m)
    (Eta.originalEtaBlock term (n + m))

bishopComplexAddRightZero :
  (x : BC.BishopComplex) →
  Eta._≈C_ x (BC._+C_ x BC.zeroC)
bishopComplexAddRightZero (BC.bishop-complex xr xi) =
  (let open RP.ℝ-Solver in
   solve 1 (λ a → a ⊜ (a ⊕ Κ 0ℚᵘ)) RP.≃-refl xr)
  ,
  (let open RP.ℝ-Solver in
   solve 1 (λ a → a ⊜ (a ⊕ Κ 0ℚᵘ)) RP.≃-refl xi)

bishopComplexAddAssoc :
  (a b c : BC.BishopComplex) →
  Eta._≈C_
    (BC._+C_ (BC._+C_ a b) c)
    (BC._+C_ a (BC._+C_ b c))
bishopComplexAddAssoc
  (BC.bishop-complex ar ai)
  (BC.bishop-complex br bi)
  (BC.bishop-complex cr ci) =
  (let open RP.ℝ-Solver in
   solve 3
     (λ x y z → (x ⊕ y) ⊕ z ⊜ x ⊕ (y ⊕ z))
     RP.≃-refl ar br cr)
  ,
  (let open RP.ℝ-Solver in
   solve 3
     (λ x y z → (x ⊕ y) ⊕ z ⊜ x ⊕ (y ⊕ z))
     RP.≃-refl ai bi ci)

-- Source-native shifted cumulative tail, ALL n,m, including n=0
-- and m=0. The proof's only index rewrites are Nat addition.
originalBishopEtaPrefixShiftedPairsExact :
  (term : Nat → BC.BishopComplex) →
  (n m : Nat) →
  Eta._≈C_
    (Eta.originalEtaPrefix term (n + m))
    (BC._+C_
      (Eta.originalEtaPrefix term n)
      (originalShiftedEtaPairs term n m))
originalBishopEtaPrefixShiftedPairsExact term n zero
  rewrite NatP.+-identityʳ n =
  bishopComplexAddRightZero (Eta.originalEtaPrefix term n)
originalBishopEtaPrefixShiftedPairsExact term n (suc m)
  rewrite NatP.+-suc n m =
  Eta.≈C-trans
    (Eta.addRightCongruent
      (originalBishopEtaPrefixShiftedPairsExact term n m)
      (Eta.originalEtaBlock term (n + m)))
    (bishopComplexAddAssoc
      (Eta.originalEtaPrefix term n)
      (originalShiftedEtaPairs term n m)
      (Eta.originalEtaBlock term (n + m)))

module OriginalRound11 (inputs : Round11.BishopCutset) where
  module Selected = Eta.OriginalRound11DirichletEta inputs

  -- The original selected Round11 source, not just an arbitrary term.
  actualOriginalRound11ShiftedEtaTailExact :
    (s : BC.BishopComplex) (n m : Nat) →
    Eta._≈C_
      (Eta.originalEtaPrefix (Selected.sourceTerms s) (n + m))
      (BC._+C_
        (Eta.originalEtaPrefix (Selected.sourceTerms s) n)
        (originalShiftedEtaPairs (Selected.sourceTerms s) n m))
  actualOriginalRound11ShiftedEtaTailExact s n m =
    originalBishopEtaPrefixShiftedPairsExact
      (Selected.sourceTerms s) n m


------------------------------------------------------------------------
-- Direct native completion on the literal pair-prefix sequence.
-- Uses the pinned Sequence.cauchy* and fast-cauchy⇒convergent API,
-- not an additional limit authority or a new analytic function.
-- Source-written only. The adjacent coordinate estimates and common
-- decay modulus are explicit remaining source obligations.
------------------------------------------------------------------------

forwardPotentialBound :
  (f P : Nat → R.ℝ) →
  (∀ n → R._≤_ (R.∣ R._-_ (f (suc n)) (f n) ∣)
                  (R._-_ (P n) (P (suc n)))) →
  ∀ n m →
  R._≤_ (R.∣ R._-_ (f (n + m)) (f n) ∣)
         (R._-_ (P n) (P (n + m)))
forwardPotentialBound f P step n zero
  rewrite NatP.+-identityʳ n =
  RP.≤-reflexive
    (RP.≃-trans (RP.∣-∣-cong (RP.+-inverseʳ (f n)))
      (RP.≃-trans
        (RP.nonNegx⇒∣x∣≃x (RP.0≤x⇒nonNegx RP.≤-refl))
        (RP.≃-symm (RP.+-inverseʳ (P n)))))
forwardPotentialBound f P step n (suc m)
  rewrite NatP.+-suc n m =
  let
    a = f (suc (n + m))
    b = f (n + m)
    c = f n
    x = P n
    y = P (n + m)
    z = P (suc (n + m))
    open RP.ℝ-Solver
  in
  RP.≤-respʳ-≃
    (solve 3 (λ x y z → (y ⊖ z) ⊕ (x ⊖ y) ⊜ x ⊖ z)
      RP.≃-refl x y z)
    (RP.≤-respˡ-≃
      (RP.∣-∣-cong
        (solve 3 (λ a b c → (a ⊖ b) ⊕ (b ⊖ c) ⊜ a ⊖ c)
          RP.≃-refl a b c))
      (RP.≤-trans
        (RP.∣x+y∣≤∣x∣+∣y∣ (R._-_ a b) (R._-_ b c))
        (RP.+-mono-≤ (step (n + m))
          (forwardPotentialBound f P step n m))))

orderedPotentialBound :
  (f P : Nat → R.ℝ) →
  (∀ n → R._≤_ (R.∣ R._-_ (f (suc n)) (f n) ∣)
                  (R._-_ (P n) (P (suc n)))) →
  ∀ n m → n ≤ m →
  R._≤_ (R.∣ R._-_ (f m) (f n) ∣) (R._-_ (P n) (P m))
orderedPotentialBound f P step n m n≤m =
  Eq.subst
    (λ j → R._≤_ (R.∣ R._-_ (f j) (f n) ∣) (R._-_ (P n) (P j)))
    (Eq.trans (NatP.+-comm n (m ∸ n)) (NatP.m∸n+n≡m n≤m))
    (forwardPotentialBound f P step n (m ∸ n))

potentialDropBelowStart :
  (P : Nat → R.ℝ) →
  (∀ n → R._≤_ R.0ℝ (P n)) →
  ∀ n m → R._≤_ (R._-_ (P n) (P m)) (P n)
potentialDropBelowStart P nonnegative n m =
  RP.≤-respʳ-≃
    (RP.≃-trans
      (RP.+-congʳ (P n) (RP.≃-symm RP.0≃-0))
      (RP.+-identityʳ (P n)))
    (RP.+-monoʳ-≤ (P n) (RP.neg-mono-≤ (nonnegative m)))

-- N-1 matches the actual vendor Cauchy constructor exactly.
DecayModulus : (Nat → R.ℝ) → Set
DecayModulus P =
  (k : Nat) → .{{_ : NonZero k}} →
  Σ Nat (λ N-1 → ∀ n → suc N-1 ≤ n →
    R._≤_ (P n) (R._⋆ (+ 1 / k)))

module CompleteScalar
  (f P : Nat → R.ℝ)
  (step : ∀ n → R._≤_ (R.∣ R._-_ (f (suc n)) (f n) ∣)
                         (R._-_ (P n) (P (suc n))))
  (nonnegative : ∀ n → R._≤_ R.0ℝ (P n))
  (modulus : DecayModulus P) where

  orderedBound :
    ∀ n m → n ≤ m →
    R._≤_ (R.∣ R._-_ (f m) (f n) ∣) (P n)
  orderedBound n m n≤m =
    RP.≤-trans (orderedPotentialBound f P step n m n≤m)
      (potentialDropBelowStart P nonnegative n m)

  bothOrders :
    ∀ m n → (k : Nat) → .{{_ : NonZero k}} →
    suc (proj₁ (modulus k)) ≤ m →
    suc (proj₁ (modulus k)) ≤ n →
    R._≤_ (R.∣ R._-_ (f m) (f n) ∣) (R._⋆ (+ 1 / k))
  bothOrders m n k mPast nPast with NatP.≤-total n m
  ... | inj₁ n≤m =
    RP.≤-trans (orderedBound n m n≤m) (proj₂ (modulus k) n nPast)
  ... | inj₂ m≤n =
    RP.≤-respˡ-≃ (RP.∣x-y∣≃∣y-x∣ (f n) (f m))
      (RP.≤-trans (orderedBound m n m≤n) (proj₂ (modulus k) m mPast))

  cauchy : Seq._isCauchy f
  cauchy = Seq.cauchy* (λ k →
    proj₁ (modulus k) , (λ m n → bothOrders m n k))

  convergent : Seq._isConvergent f
  convergent = Seq.fast-cauchy⇒convergent cauchy

  value : R.ℝ
  value = Seq.lim convergent

  converges : Seq._ConvergesTo_ f value
  converges = proj₂ convergent

  -- The same potential controls the actual completed limit for every
  -- cutoff, not merely the sampled dyadic cutoffs.
  limitError : ∀ n → R._≤_ (R.∣ R._-_ value (f n) ∣) (P n)
  limitError n =
    let
      shifted : Nat → R.ℝ
      shifted j = f (j + n)
      shiftedConverges : Seq._ConvergesTo_ shifted value
      shiftedConverges = Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
        (Seq.subseq* ((λ j → j + n) ,
          (λ j → RP.≃-refl) ,
          (λ j → NatP.n<1+n (j + n))))
        convergent
      differenceConverges : Seq._ConvergesTo_
        (λ j → R._-_ (shifted j) (f n)) (R._-_ value (f n))
      differenceConverges = Seq.xₙ+yₙ→x₀+y₀
        (value , shiftedConverges)
        (R.-_ (f n) , Seq.xₙ≃c⇒xₙ→c (λ j → RP.≃-refl))
      absoluteConvergent : Seq._isConvergent
        (λ j → R.∣ R._-_ (shifted j) (f n) ∣)
      absoluteConvergent =
        R.∣ R._-_ value (f n) ∣ ,
        Seq.∣xₙ∣→∣x₀∣ (R._-_ value (f n) , differenceConverges)
    in
    Seq.xₙ≤y⇒limxₙ≤y
      (λ j → orderedBound n (j + n) (NatP.m≤n+m n j))
      absoluteConvergent

-- Actual eta prefix step has no analytic input beyond the literal
-- coordinate bound on the original paired term.
coordinatePrefixStep :
  (term : Nat → BC.BishopComplex) →
  (coord : BC.BishopComplex → R.ℝ) →
  ((x y : BC.BishopComplex) →
    R._≃_ (coord (BC._+C_ x y)) (R._+_ (coord x) (coord y))) →
  (P : Nat → R.ℝ) →
  (∀ n → R._≤_ (R.∣ coord (Eta.originalEtaBlock term n) ∣)
                 (R._-_ (P n) (P (suc n)))) →
  ∀ n →
  R._≤_
    (R.∣ R._-_ (coord (Eta.originalEtaPrefix term (suc n)))
                 (coord (Eta.originalEtaPrefix term n)) ∣)
    (R._-_ (P n) (P (suc n)))
coordinatePrefixStep term coord addLaw P bound n =
  let
    a = coord (Eta.originalEtaPrefix term n)
    b = coord (Eta.originalEtaBlock term n)
    open RP.ℝ-Solver
  in
  RP.≤-respˡ-≃
    (RP.∣-∣-cong
      (RP.≃-symm
        (RP.≃-trans
          (RP.+-congˡ (R.-_ a)
            (addLaw (Eta.originalEtaPrefix term n) (Eta.originalEtaBlock term n)))
          (solve 2 (λ x y → (x ⊕ y) ⊖ x ⊜ y) RP.≃-refl a b))))
    (bound n)

module CompleteOriginalRound11
  (inputs : Round11.BishopCutset)
  (s : BC.BishopComplex)
  (P : Nat → R.ℝ)
  (realBound : ∀ n → R._≤_
    (R.∣ BC.re (Eta.originalEtaBlock
      (Eta.OriginalRound11DirichletEta.sourceTerms inputs s) n) ∣)
    (R._-_ (P n) (P (suc n))))
  (imagBound : ∀ n → R._≤_
    (R.∣ BC.im (Eta.originalEtaBlock
      (Eta.OriginalRound11DirichletEta.sourceTerms inputs s) n) ∣)
    (R._-_ (P n) (P (suc n))))
  (nonnegative : ∀ n → R._≤_ R.0ℝ (P n))
  (modulus : DecayModulus P) where

  private
    term = Eta.OriginalRound11DirichletEta.sourceTerms inputs s
    prefix = Eta.originalEtaPrefix term

  module RealLimit = CompleteScalar
    (λ n → BC.re (prefix n)) P
    (coordinatePrefixStep term BC.re
      (λ { (BC.bishop-complex a b) (BC.bishop-complex c d) → RP.≃-refl })
      P realBound)
    nonnegative modulus

  module ImagLimit = CompleteScalar
    (λ n → BC.im (prefix n)) P
    (coordinatePrefixStep term BC.im
      (λ { (BC.bishop-complex a b) (BC.bishop-complex c d) → RP.≃-refl })
      P imagBound)
    nonnegative modulus

  originalEtaValue : BC.BishopComplex
  originalEtaValue = BC.bishop-complex RealLimit.value ImagLimit.value

  originalEtaConverges :
    Seq._ConvergesTo_ (λ n → BC.re (prefix n)) (BC.re originalEtaValue)
    ×
    Seq._ConvergesTo_ (λ n → BC.im (prefix n)) (BC.im originalEtaValue)
  originalEtaConverges = RealLimit.converges , ImagLimit.converges

  originalEtaLimitError :
    ∀ n →
    R._≤_ (R.∣ R._-_ (BC.re originalEtaValue) (BC.re (prefix n)) ∣) (P n)
    ×
    R._≤_ (R.∣ R._-_ (BC.im originalEtaValue) (BC.im (prefix n)) ∣) (P n)
  originalEtaLimitError n = RealLimit.limitError n , ImagLimit.limitError n


------------------------------------------------------------------------
-- Construct the COMMON decay modulus on the original Nat-log.
-- Only the actual adjacent-coordinate inequalities remain analytic
-- inputs of the selected eta completion below.
------------------------------------------------------------------------

originalDecay : R.ℝ → Nat → R.ℝ
originalDecay δ n =
  Exp.bishopExp (R._*_ (R.-_ δ) (Terms.sourceCanonicalNatLogCandidate n))

originalDecayZero : ∀ δ → R._≃_ (originalDecay δ zero) R.1ℝ
originalDecayZero δ =
  RP.≃-trans
    (ExpCong.bishopExpCongruent (RP.*-zeroʳ (R.-_ δ)))
    Pos.bishopExpZero

originalDecayPositive :
  ∀ δ → R._<_ R.0ℝ δ → ∀ n →
  R._<_ R.0ℝ (originalDecay δ n)
originalDecayPositive δ δPositive zero =
  RP.<-respʳ-≃ (RP.≃-symm (originalDecayZero δ)) Neg.onePositive
originalDecayPositive δ δPositive (suc n) =
  let
    L = Terms.sourceCanonicalNatLogCandidate (suc n)
    productPositive =
      RP.posx⇒0<x
        (RP.posx,y⇒posx*y (RP.0<x⇒posx δPositive)
          (RP.0<x⇒posx (Terms.sourceCanonicalNatLogSuccessorPositive n)))
  in
  RP.<-respʳ-≃
    (ExpCong.bishopExpCongruent (RP.neg-distribˡ-* δ L))
    (Neg.negativeExpPositive productPositive)

originalDecayRatioBelowOne :
  ∀ δ → R._<_ R.0ℝ δ →
  R._<_ (originalDecay δ (suc zero)) R.1ℝ
originalDecayRatioBelowOne δ δPositive =
  let
    L = Terms.sourceCanonicalNatLogCandidate (suc zero)
    productPositive =
      RP.posx⇒0<x
        (RP.posx,y⇒posx*y (RP.0<x⇒posx δPositive)
          (RP.0<x⇒posx (Terms.sourceCanonicalNatLogSuccessorPositive zero)))
  in
  RP.<-respˡ-≃
    (ExpCong.bishopExpCongruent (RP.neg-distribˡ-* δ L))
    (Neg.negativeExpBelowOne productPositive)

originalDecayDecreasing :
  ∀ δ → R._<_ R.0ℝ δ → ∀ {i j} → i ≤ j →
  R._≤_ (originalDecay δ j) (originalDecay δ i)
originalDecayDecreasing δ δPositive {i} {j} indices =
  let
    Li = Terms.sourceCanonicalNatLogCandidate i
    Lj = Terms.sourceCanonicalNatLogCandidate j
    productOrder = RP.*-monoˡ-≤-nonNeg
      (Log.canonicalNatLogMonotone indices)
      (RP.pos⇒nonNeg (RP.0<x⇒posx δPositive))
    exponentOrder =
      RP.≤-respˡ-≃ (RP.neg-distribˡ-* δ Lj)
        (RP.≤-respʳ-≃ (RP.neg-distribˡ-* δ Li)
          (RP.neg-mono-≤ productOrder))
  in
  ExpProduct.bishopExpWeakOrderFromNonnegativeValue
    (RP.pos⇒nonNeg (RP.0<x⇒posx (originalDecayPositive δ δPositive j)))
    exponentOrder

-- Zero-based index of the positive integer 2^k.
dyadicIndex : Nat → Nat
dyadicIndex zero = zero
dyadicIndex (suc k) = suc (dyadicIndex k + dyadicIndex k)

originalDecayDyadicStep :
  ∀ δ n →
  R._≃_
    (originalDecay δ (suc (n + n)))
    (R._*_ (originalDecay δ (suc zero)) (originalDecay δ n))
originalDecayDyadicStep δ n =
  let
    L = Terms.sourceCanonicalNatLogCandidate
    x = R.-_ δ
  in
  RP.≃-trans
    (ExpCong.bishopExpCongruent
      (RP.≃-trans (RP.*-congˡ (Log.canonicalNatLogDyadic n))
        (RP.*-distribˡ-+ x (L (suc zero)) (L n))))
    (ExpProduct.bishopExpAdd
      (R._*_ x (L (suc zero))) (R._*_ x (L n)))

originalDecayAtDyadicIndex :
  ∀ δ k →
  R._≃_ (originalDecay δ (dyadicIndex k))
    (R.pow (originalDecay δ (suc zero)) k)
originalDecayAtDyadicIndex δ zero = originalDecayZero δ
originalDecayAtDyadicIndex δ (suc k) =
  RP.≃-trans (originalDecayDyadicStep δ (dyadicIndex k))
    (RP.≃-trans
      (RP.*-cong RP.≃-refl (originalDecayAtDyadicIndex δ k))
      (RP.*-comm (originalDecay δ (suc zero))
        (R.pow (originalDecay δ (suc zero)) k)))

originalEtaDecayPotential : R.ℝ → R.ℝ → Nat → R.ℝ
originalEtaDecayPotential C δ n =
  R._*_ C (originalDecay δ (Eta.twice n))

module NativeDecay
  (C δ : R.ℝ)
  (Cnonnegative : R.NonNegative C)
  (δPositive : R._<_ R.0ℝ δ) where

  private
    q = originalDecay δ (suc zero)
    qPositive = originalDecayPositive δ δPositive (suc zero)
    qBelowOne = originalDecayRatioBelowOne δ δPositive
    P = originalEtaDecayPotential C δ
    scaled = Geo.scaledGeometricTerm C q

  potentialNonnegative : ∀ n → R._≤_ R.0ℝ (P n)
  potentialNonnegative n =
    RP.nonNegx⇒0≤x
      (RP.nonNegx,y⇒nonNegx*y Cnonnegative
        (RP.pos⇒nonNeg (RP.0<x⇒posx
          (originalDecayPositive δ δPositive (Eta.twice n)))))

  scaledConvergesZero : Seq._ConvergesTo_ scaled R.0ℝ
  scaledConvergesZero =
    Seq.∑xₙisConvergent⇒xₙ→0 scaled
      (Geo.scaledGeometricSeriesConvergent
        q C qPositive qBelowOne Cnonnegative)

  potentialAtLeastDyadicIndex :
    ∀ k n → dyadicIndex k ≤ Eta.twice n →
    R._≤_ (P n) (scaled k)
  potentialAtLeastDyadicIndex k n indices =
    RP.≤-respʳ-≃ (RP.*-cong RP.≃-refl (originalDecayAtDyadicIndex δ k))
      (RP.*-monoˡ-≤-nonNeg
        (originalDecayDecreasing δ δPositive indices)
        Cnonnegative)

  -- Construct one cutoff for both coordinates, independent of s.
  potentialModulus : DecayModulus P
  potentialModulus k =
    let
      receipt = Seq.convergence-getter (R.0ℝ , scaledConvergesZero) k
      K = suc (proj₁ receipt)
      index = dyadicIndex K
      magnitudeEq =
        RP.≃-trans
          (RP.∣-∣-cong (RP.≃-trans
            (RP.+-congʳ (scaled K) (RP.≃-symm RP.0≃-0))
            (RP.+-identityʳ (scaled K))))
          (RP.nonNegx⇒∣x∣≃x
            (Geo.scaledGeometricTermNonnegative Cnonnegative qPositive K))
      small =
        RP.≤-respˡ-≃ magnitudeEq (proj₂ receipt K NatP.≤-refl)
    in
    index , (λ n past →
      RP.≤-trans
        (potentialAtLeastDyadicIndex K n
          (NatP.≤-trans (NatP.n≤1+n index)
            (NatP.≤-trans past (NatP.m≤m+n n n))))
        small)

module CompleteOriginalFromNativeDecay
  (inputs : Round11.BishopCutset)
  (s : BC.BishopComplex)
  (C δ : R.ℝ)
  (Cnonnegative : R.NonNegative C)
  (δPositive : R._<_ R.0ℝ δ)
  (realBound : ∀ n → R._≤_
    (R.∣ BC.re (Eta.originalEtaBlock
      (Eta.OriginalRound11DirichletEta.sourceTerms inputs s) n) ∣)
    (R._-_ (originalEtaDecayPotential C δ n)
             (originalEtaDecayPotential C δ (suc n)))))
  (imagBound : ∀ n → R._≤_
    (R.∣ BC.im (Eta.originalEtaBlock
      (Eta.OriginalRound11DirichletEta.sourceTerms inputs s) n) ∣)
    (R._-_ (originalEtaDecayPotential C δ n)
             (originalEtaDecayPotential C δ (suc n))))) where

  module Decay = NativeDecay C δ Cnonnegative δPositive
  module Completed = CompleteOriginalRound11 inputs s
    (originalEtaDecayPotential C δ) realBound imagBound
    Decay.potentialNonnegative Decay.potentialModulus

  open Completed public using
    (originalEtaValue; originalEtaConverges; originalEtaLimitError)
