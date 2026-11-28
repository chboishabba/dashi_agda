module DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationReflectionExact where

-- SOURCE-WRITTEN, kernel pending. The generic original Hecke reflection
-- is applied to every integer parameter of the full candidate matrix.
-- Keep the exact UnitGate and SectorGate witnesses explicit. No
-- specialization or analytic identity is asserted from a digest.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Data.Fin.Base as Fin using (Fin)
open import Data.Integer.Base as Z using (ℤ)
open import Data.Product.Base using (proj₁; proj₂)
open import Data.Unit.Base using (tt)
open import Data.Rational.Unnormalised using (ℚᵘ)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41ConvergentSeriesExact as Eval
import DASHI.Moonshine.CM163BishopHecke41FinitePrefixReflectionExact as Ref
import DASHI.Moonshine.CM163BishopHecke41PacketPrefixWeldExact as Weld
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41SparseRingExact as Sparse
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
import DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact as Lit
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ArbitrarySliceSeriesExact as Arbitrary
import DASHI.Moonshine.CM163BishopHecke41IntegerSpecializationExact as Special
import DASHI.Moonshine.CM163BishopHecke41MatrixSymmetryExact as Mat
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G using (Series; _≈s_; _⊖s_; constant; subCong; transS)
open Ref using (lift; prefixRestrict)
open U using (PrefixEq)
open Actual using (expand; delay)
open R41 using (restrict; stride; Sector)
open C using (_≈C_)
open Comp using (complexTrans)

constantRead : ∀ y → lift (Cert.constant y) ≈s constant (I.embed y)
constantRead y zero = P.≃-refl
constantRead y (suc n) = P.≃-refl

hZ gZ : ℤ → Nat → ℤ
hZ y n = Z._-_ (Cert.j n) (Cert.delay 1 (Cert.constant y) n)
gZ y n = Z._-_ (Cert.expand Cert.j n) (Cert.delay 41 (Cert.constant y) n)

hRead : ∀ y → PrefixEq (lift Cert.j) D.Junit 3322 →
  PrefixEq (lift (hZ y)) (Arbitrary.hY (I.embed y)) 1722
hRead y hj = Weld.subRead Cert.j (Cert.delay 1 (Cert.constant y))
  D.Junit (delay 1 (constant (I.embed y))) 1722
  (prefixRestrict hj 1722 (from-yes (1722 NP.≤? 3322)))
  (Weld.delayRead (Cert.constant y) (constant (I.embed y)) 1721 1
    (λ n hn → constantRead y n))

gSector : ∀ y → Sector (Arbitrary.gY (I.embed y))
gSector y = Sparse.sectorSub _ _
  (Sparse.sectorExpand (expand D.Junit))
  (Sparse.sectorDelay 41 (constant (I.embed y)) (Sparse.constantSector (I.embed y)))

gRestrict : ∀ y → restrict (Arbitrary.gY (I.embed y)) ≈s
  (expand D.Junit ⊖s delay 41 (constant (I.embed y)))
gRestrict y = subCong (Sparse.restrictExpand (expand D.Junit))
  (transS (Sparse.restrictDelay 41 (constant (I.embed y)))
    (Lit.delayCong 41 (Sparse.restrictConstant (I.embed y))))

gRead : ∀ y → PrefixEq (lift Cert.j) D.Junit 42 →
  PrefixEq (lift (gZ y)) (restrict (Arbitrary.gY (I.embed y))) 42
gRead y hj n hn = P.≃-trans (Weld.subRead _ _ _ _ 42
  (Lit.expandPrefix Cert.j D.Junit 42 hj)
  (Lit.delayPrefix (Cert.constant y) (constant (I.embed y)) 42 41
    (λ k hk → constantRead y k)) n hn)
  (P.≃-symm (gRestrict y n))

integralList : ∀ {n} (f : Fin n → ℤ) → Lit.Integral (Special.columnList f)
integralList {zero} f = tt
integralList {suc n} f = integralList (λ i → f (Fin.suc i))

module At (inputs : Round11.BishopCutset) where
  module L = Lit.At inputs
  module Rf = Ref.At inputs
  module A0 = Arbitrary.At inputs
  module S0 = Special.At inputs

  module For (c : Mat.Coefficient) (y : ℤ) where
    module S = S0.For c y
    module Y = A0.For (I.embed y)
    module B = Rf.For Y.h (Arbitrary.hY0 (I.embed y))

    cs = Special.column c y
    l = Cert.slot (Cert.candidateL 1722 (hZ y))
    a = Cert.slot (Cert.candidateN 42 l)

    Gate : Set
    Gate = Cert.SectorGate 42 (hZ y) (gZ y) l a cs Cert.j

    gate? : Dec Gate
    gate? = Cert.sectorDec 42 (hZ y) (gZ y) l a cs Cert.j

    logRead : L.W.UnitGate → Gate →
      PrefixEq (lift l) (E.Log.ell Y.h (Arbitrary.hY0 (I.embed y))) 1722
    logRead hu hg = Ref.logRead Y.h (Arbitrary.hY0 (I.embed y)) (hZ y) l 1722
      (hRead y (L.W.jPrefix hu)) (proj₁ hg)

    driverRead : L.W.UnitGate → Gate → PrefixEq (lift (Cert.traceDriver l)) B.A.driver 42
    driverRead hu hg n hn = logRead hu hg (stride n) (NP.*-monoʳ-≤ 41 hn)

    normRead : L.W.UnitGate → Gate → ∀ n → n ≤ 42 →
      B.A.reduced n ≈C E.lift (lift a) n
    normRead hu hg = B.complexNormRead 42 (Cert.traceDriver l) a
      (driverRead hu hg) (Weld.normHead 42 l) (proj₁ (proj₂ hg))

    j42 : L.W.UnitGate → PrefixEq (lift Cert.j) D.Junit 42
    j42 hu = prefixRestrict (L.W.jPrefix hu) 42 (from-yes (42 NP.≤? 3322))

    reflect : L.W.UnitGate → Gate → ∀ n → n ≤ 1722 →
      Y.series n ≈C E.lift (Actual.column cs) n
    reflect hu hg = L.reflectProduct Y.g B.A.raw cs (gZ y) a 42
      (gSector y) B.A.sectorNorm (integralList (Special.columnCoefficient c y))
      (gRead y (j42 hu)) (normRead hu hg)
      (Lit.columnRead Cert.j 42 cs (integralList (Special.columnCoefficient c y)) (j42 hu))
      (proj₂ (proj₂ hg))

    zeroPrefix : L.W.UnitGate → Gate → S.S.PrefixGate
    zeroPrefix hu hg n hn = complexTrans
      (A.subCCongruent (reflect hu hg n hn) (C.≈C-refl _)) (Prod.differenceSelf _)

    poleRemoved : L.W.UnitGate → Gate → ∀ p →
      S.S.residual p ≈C A._*C_ (A0.A0.t p) (Eval.value (S.S.tail p))
    poleRemoved hu hg = S.S.poleRemoved (zeroPrefix hu hg)
