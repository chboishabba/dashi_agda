module DASHI.Moonshine.CM163BishopHecke41PacketPrefixWeldExact where

-- SOURCE-WRITTEN, kernel pending. Bind the precise 3322/1722 J
-- prefixes to the actual two ramified H polynomials, then transport
-- the 3363/1723 integer residual witnesses through native uniqueness.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s; _<_)
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_; _/_; m≡m%n+[m/n]*n)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Relation.Binary.PropositionalEquality using (cong; sym; subst)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (_≃_; _⋆)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41FinitePrefixReflectionExact as Ref
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ReducedNormFlowExact as Reduced
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G
open U using (PrefixEq)
open Ref using (lift; prefixRestrict)

dropAdd : ∀ k {a b} → k + a ≤ k + b → a ≤ b
dropAdd zero h = h
dropAdd (suc k) (s≤s h) = dropAdd k h

strideReflect : ∀ {a b} → R41.stride a ≤ R41.stride b → a ≤ b
strideReflect {zero} {b} h = z≤n
strideReflect {suc a} {zero} ()
strideReflect {suc a} {suc b} h = s≤s (strideReflect (dropAdd 41 h))

quotBound : ∀ n D0 → n ≤ R41.stride D0 → n / 41 ≤ D0
quotBound n D0 h = strideReflect
  (NP.≤-trans
    (subst (λ k → R41.stride (n / 41) ≤ k) (sym (m≡m%n+[m/n]*n n 41))
      (NP.m≤n+m (R41.stride (n / 41)) (n % 41))) h)

expandRead : ∀ a f D0 → PrefixEq (lift a) f D0 →
  PrefixEq (lift (Cert.expand a)) (Actual.expand f) (R41.stride D0)
expandRead a f D0 h n hn with n % 41 NP.≟ zero
... | yes _ = h (n / 41) (quotBound n D0 hn)
... | no _ = P.≃-refl

delayRead : ∀ a f D0 k → PrefixEq (lift a) f D0 →
  PrefixEq (lift (Cert.delay k a)) (Actual.delay k f) (k + D0)
delayRead a f D0 zero h n hn = h n hn
delayRead a f D0 (suc k) h zero hn = P.≃-refl
delayRead a f D0 (suc k) h (suc n) (s≤s hn) = delayRead a f D0 k h n hn

subRead : ∀ a b f g D0 → PrefixEq (lift a) f D0 → PrefixEq (lift b) g D0 →
  PrefixEq (lift (λ n → Z._-_ (a n) (b n))) (f ⊖s g) D0
subRead a b f g D0 ha hb n hn = P.≃-trans (Ref.embedSub (a n) (b n))
  (P.+-cong (ha n hn) (P.-‿cong (hb n hn)))

constantK : lift (Cert.constant Cert.K) ≈s G.constant (Shift.Kq ⋆)
constantK zero = P.≃-refl
constantK (suc n) = P.≃-refl

hDiagRead : PrefixEq (lift Cert.j) D.Junit 3322 →
  PrefixEq (lift (Cert.hDiag Cert.j)) Actual.hDiag 3362
hDiagRead hj = subRead (Cert.expand Cert.j) (Cert.delay 40 Cert.j)
  (Actual.expand D.Junit) (Actual.delay 40 D.Junit) 3362
  (expandRead Cert.j D.Junit 82 (prefixRestrict hj 82 (from-yes (82 NP.≤? 3322))))
  (delayRead Cert.j D.Junit 3322 40 hj)

hSliceRead : PrefixEq (lift Cert.j) D.Junit 3322 →
  PrefixEq (lift (Cert.hSlice Cert.j)) Actual.hSlice 1722
hSliceRead hj = subRead Cert.j (Cert.delay 1 (Cert.constant Cert.K))
  D.Junit (Actual.delay 1 (G.constant (Shift.Kq ⋆))) 1722
  (prefixRestrict hj 1722 NP.≤-refl-bound)
  (delayRead (Cert.constant Cert.K) (G.constant (Shift.Kq ⋆)) 1721 1
    (λ n hn → constantK n))

-- Head proof for candidate generation does not normalize all the
-- large integer coefficients merely to establish the constant mode.
headBuild : ∀ f a as k n → Cert.slot (Cert.buildFrom f (a ∷ as) k n) zero ≡ a
headBuild f a as k zero = refl
headBuild f a as k (suc n) = headBuild f a (as ++ (f (a ∷ as) k ∷ [])) (suc k) n

normHead : ∀ D0 l → Cert.slot (Cert.candidateN D0 l) zero ≡ (+ 1)
normHead D0 l = headBuild _ (+ 1) [] 1 D0

module At (inputs : Round11.BishopCutset) where
  module Binding = Ref.At inputs
  module Diag = Binding.For Actual.hDiag Actual.hDiag0
  module Slice = Binding.For Actual.hSlice Actual.hSlice0

  UnitGate : Set
  UnitGate = Cert.UnitGate 3322 Cert.u Cert.j
  DiagonalGate : Set
  DiagonalGate = Cert.SectorGate 82 (Cert.hDiag Cert.j) (Cert.gDiag Cert.j)
    Cert.lD Cert.nD Packet.diagonal Cert.j
  SliceGate : Set
  SliceGate = Cert.SectorGate 42 (Cert.hSlice Cert.j) (Cert.gSlice Cert.j)
    Cert.lS Cert.nS Packet.slice Cert.j

  jPrefix : UnitGate → PrefixEq (lift Cert.j) D.Junit 3322
  jPrefix = Ref.jRead 3322 Cert.u Cert.j

  diagLog : UnitGate → DiagonalGate →
    PrefixEq (lift Cert.lD) (E.Log.ell Actual.hDiag Actual.hDiag0) 3362
  diagLog hu hd = Ref.logRead Actual.hDiag Actual.hDiag0 (Cert.hDiag Cert.j) Cert.lD 3362
    (hDiagRead (jPrefix hu)) (proj₁ hd)

  sliceLog : UnitGate → SliceGate →
    PrefixEq (lift Cert.lS) (E.Log.ell Actual.hSlice Actual.hSlice0) 1722
  sliceLog hu hs = Ref.logRead Actual.hSlice Actual.hSlice0 (Cert.hSlice Cert.j) Cert.lS 1722
    (hSliceRead (jPrefix hu)) (proj₁ hs)

  diagDriver : UnitGate → DiagonalGate → PrefixEq (lift (Cert.traceDriver Cert.lD)) Diag.A.driver 82
  diagDriver hu hd n hn = diagLog hu hd (R41.stride n) (NP.*-monoʳ-≤ 41 hn)

  sliceDriver : UnitGate → SliceGate → PrefixEq (lift (Cert.traceDriver Cert.lS)) Slice.A.driver 42
  sliceDriver hu hs n hn = sliceLog hu hs (R41.stride n) (NP.*-monoʳ-≤ 41 hn)

  diagNorm : UnitGate → DiagonalGate → PrefixEq (lift Cert.nD) Diag.A.real 82
  diagNorm hu hd = Diag.normRead 82 (Cert.traceDriver Cert.lD) Cert.nD
    (diagDriver hu hd) (normHead 82 Cert.lD) (proj₁ (proj₂ hd))

  sliceNorm : UnitGate → SliceGate → PrefixEq (lift Cert.nS) Slice.A.real 42
  sliceNorm hu hs = Slice.normRead 42 (Cert.traceDriver Cert.lS) Cert.nS
    (sliceDriver hu hs) (normHead 42 Cert.lS) (proj₁ (proj₂ hs))

  diagComplex : UnitGate → DiagonalGate → ∀ n → n ≤ 82 →
    C._≈C_ (Diag.A.reduced n) (E.lift (lift Cert.nD) n)
  diagComplex hu hd = Diag.complexNormRead 82 (Cert.traceDriver Cert.lD) Cert.nD
    (diagDriver hu hd) (normHead 82 Cert.lD) (proj₁ (proj₂ hd))

  sliceComplex : UnitGate → SliceGate → ∀ n → n ≤ 42 →
    C._≈C_ (Slice.A.reduced n) (E.lift (lift Cert.nS) n)
  sliceComplex hu hs = Slice.complexNormRead 42 (Cert.traceDriver Cert.lS) Cert.nS
    (sliceDriver hu hs) (normHead 42 Cert.lS) (proj₁ (proj₂ hs))
