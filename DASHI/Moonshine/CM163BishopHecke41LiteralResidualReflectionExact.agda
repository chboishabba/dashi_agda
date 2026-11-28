module DASHI.Moonshine.CM163BishopHecke41LiteralResidualReflectionExact where

-- SOURCE-WRITTEN, kernel pending. The actual diagonal and fixed slice
-- residuals vanish through the precise ramified cutoff IF the exact
-- finite integer gates are inhabited. No analytic equality asserted.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
import Data.Nat.Properties as NP
open import Data.Nat.DivMod using (_%_; _/_)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.List.Base using (List; []; _∷_; length)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Unit.Base using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Relation.Binary.PropositionalEquality using (subst; sym)
import Data.Rational.Unnormalised as Q
import Real as R
open R using (_≃_; _⋆)
import RealProperties as P
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketExact as Packet
import DASHI.Moonshine.JInvariantBishopCM163LiteralPacketShiftExact as Shift
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41FinitePrefixReflectionExact as Ref
import DASHI.Moonshine.CM163BishopHecke41PacketPrefixWeldExact as Weld
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41SparseRingExact as Sparse
import DASHI.Moonshine.CM163BishopHecke41LiteralNormalizedCoefficientsExact as Actual
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as E
import DASHI.Moonshine.CM163BishopHecke41ReducedNormFlowExact as Red
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41ProductExact as Prod
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G
open Ref using (lift; prefixRestrict)
open U using (PrefixEq)
open Actual using (expand; delay)
open R41 using (restrict; stride; Sector)
open C using (_≈C_)
open Comp using (complexTrans; complexSym)

Integral : List Q.ℚᵘ → Set
Integral [] = ⊤
Integral (Q.mkℚᵘ z zero ∷ cs) = Integral cs
Integral (Q.mkℚᵘ z (suc d) ∷ cs) = ⊥

integral? : ∀ cs → Dec (Integral cs)
integral? [] = yes tt
integral? (Q.mkℚᵘ z zero ∷ cs) = integral? cs
integral? (Q.mkℚᵘ z (suc d) ∷ cs) = no (λ x → x)

diagIntegral : Integral Packet.diagonal
diagIntegral = from-yes (integral? Packet.diagonal)
sliceIntegral : Integral Packet.slice
sliceIntegral = from-yes (integral? Packet.slice)

columnQ : List Q.ℚᵘ → Series
columnQ [] = H.zeroSeries
columnQ (c ∷ cs) = scale (c ⋆) (H.power D.Junit (length cs)) ⊕s delay 1 (columnQ cs)

columnSector : ∀ cs → Sector (Actual.column cs)
columnSector [] = Sparse.sectorZero
columnSector (c ∷ cs) = Sparse.sectorAdd _ _
  (Sparse.sectorScale (c ⋆) _ (Sparse.sectorPower (expand D.Junit) (Sparse.sectorExpand D.Junit) (length cs)))
  (Sparse.sectorProduct Actual.t41 (Actual.column cs) (Sparse.monoSector 1) (columnSector cs))

delayCong : ∀ k {f g} → f ≈s g → delay k f ≈s delay k g
delayCong zero h n = h n
delayCong (suc k) h zero = P.≃-refl
delayCong (suc k) h (suc n) = delayCong k h n

powerCong : ∀ {f g} → f ≈s g → ∀ k → H.power f k ≈s H.power g k
powerCong h zero = reflS
powerCong h (suc k) = mulCong h (powerCong h k)

columnRestrict : ∀ cs → restrict (Actual.column cs) ≈s columnQ cs
columnRestrict [] n = P.≃-refl
columnRestrict (c ∷ cs) = addCong
  (λ n → P.*-congˡ (transS
    (Sparse.restrictPower (expand D.Junit) (Sparse.sectorExpand D.Junit) (length cs))
    (powerCong (Sparse.restrictExpand D.Junit) (length cs)) n))
  (transS (λ n → Sparse.monoMul 41 (Actual.column cs) (stride n))
    (transS (Sparse.restrictDelay 1 (Actual.column cs)) (delayCong 1 (columnRestrict cs))))

gDiagQ gSliceQ : Series
gDiagQ = delay 40 D.Junit ⊖s expand D.Junit
gSliceQ = expand D.Junit ⊖s delay 41 (G.constant (Shift.Kq ⋆))

gDiagSector : Sector Actual.gDiag
gDiagSector = Sparse.sectorSub _ _
  (Sparse.sectorDelay 40 (expand D.Junit) (Sparse.sectorExpand D.Junit))
  (Sparse.sectorExpand (expand D.Junit))

gSliceSector : Sector Actual.gSlice
gSliceSector = Sparse.sectorSub _ _
  (Sparse.sectorExpand (expand D.Junit))
  (Sparse.sectorDelay 41 (G.constant (Shift.Kq ⋆)) (Sparse.constantSector (Shift.Kq ⋆)))

gDiagRestrict : restrict Actual.gDiag ≈s gDiagQ
gDiagRestrict = subCong
  (transS (Sparse.restrictDelay 40 (expand D.Junit)) (delayCong 40 (Sparse.restrictExpand D.Junit)))
  (Sparse.restrictExpand (expand D.Junit))

gSliceRestrict : restrict Actual.gSlice ≈s gSliceQ
gSliceRestrict = subCong (Sparse.restrictExpand (expand D.Junit))
  (transS (Sparse.restrictDelay 41 (G.constant (Shift.Kq ⋆)))
    (delayCong 41 (Sparse.restrictConstant (Shift.Kq ⋆))))

delayPrefix : ∀ a f D0 k → PrefixEq (lift a) f D0 →
  PrefixEq (lift (Cert.delay k a)) (delay k f) D0
delayPrefix a f D0 k h = prefixRestrict (Weld.delayRead a f D0 k h) D0 (NP.m≤n+m D0 k)

expandPrefix : ∀ a f D0 → PrefixEq (lift a) f D0 →
  PrefixEq (lift (Cert.expand a)) (expand f) D0
expandPrefix a f D0 h = prefixRestrict (Weld.expandRead a f D0 h) D0 (NP.m≤m*n D0 41)

gDiagRead : ∀ D0 → PrefixEq (lift Cert.j) D.Junit D0 →
  PrefixEq (lift (Cert.gDiag Cert.j)) (restrict Actual.gDiag) D0
gDiagRead D0 hj n hn = P.≃-trans (Weld.subRead _ _ _ _ D0
  (delayPrefix Cert.j D.Junit D0 40 hj) (expandPrefix Cert.j D.Junit D0 hj) n hn)
  (P.≃-symm (gDiagRestrict n))

gSliceRead : ∀ D0 → PrefixEq (lift Cert.j) D.Junit D0 →
  PrefixEq (lift (Cert.gSlice Cert.j)) (restrict Actual.gSlice) D0
gSliceRead D0 hj n hn = P.≃-trans (Weld.subRead _ _ _ _ D0
  (expandPrefix Cert.j D.Junit D0 hj)
  (delayPrefix (Cert.constant Cert.K) (G.constant (Shift.Kq ⋆)) D0 41 (λ k hk → Weld.constantK k)) n hn)
  (P.≃-symm (gSliceRestrict n))

powerRead : ∀ a f D0 k → PrefixEq (lift a) f D0 →
  PrefixEq (lift (Cert.power a k)) (H.power f k) D0
powerRead a f D0 zero h zero hn = P.≃-refl
powerRead a f D0 zero h (suc n) hn = P.≃-refl
powerRead a f D0 (suc k) h n hn = Ref.rowReflect a (Cert.power a k) f (H.power f k) n
  (prefixRestrict h n hn) (prefixRestrict (powerRead a f D0 k h) n hn)

columnReadQ : ∀ a D0 cs → Integral cs → PrefixEq (lift a) D.Junit D0 →
  PrefixEq (lift (Cert.column a cs)) (columnQ cs) D0
columnReadQ a D0 [] ok hj n hn = P.≃-refl
columnReadQ a D0 (Q.mkℚᵘ c zero ∷ cs) ok hj n hn =
  P.≃-trans (I.embedAdd _ _)
    (P.+-cong
      (P.≃-trans (I.embedMul c (Cert.power a (length cs) n))
        (P.*-congˡ (powerRead a D.Junit D0 (length cs) hj n hn)))
      (delayPrefix (Cert.column a cs) (columnQ cs) D0 1 (columnReadQ a D0 cs ok hj) n hn))
columnReadQ a D0 (Q.mkℚᵘ c (suc d) ∷ cs) () hj

columnRead : ∀ a D0 cs → Integral cs → PrefixEq (lift a) D.Junit D0 →
  PrefixEq (lift (Cert.column a cs)) (restrict (Actual.column cs)) D0
columnRead a D0 cs ok hj n hn =
  P.≃-trans (columnReadQ a D0 cs ok hj n hn) (P.≃-symm (columnRestrict cs n))

liftSector : ∀ f → Sector f → R41.SectorC (E.lift f)
liftSector f hf n hn = hf n hn , P.≃-refl

complexSectorProduct : ∀ a b → R41.SectorC a → R41.SectorC b → R41.SectorC (N._⊗c_ a b)
complexSectorProduct a b ha hb n hn =
  Sparse.sectorSub _ _
    (Sparse.sectorProduct (C.realTerms a) (C.realTerms b) (λ k hk → proj₁ (ha k hk)) (λ k hk → proj₁ (hb k hk)))
    (Sparse.sectorProduct (C.imagTerms a) (C.imagTerms b) (λ k hk → proj₂ (ha k hk)) (λ k hk → proj₂ (hb k hk))) n hn ,
  Sparse.sectorAdd _ _
    (Sparse.sectorProduct (C.realTerms a) (C.imagTerms b) (λ k hk → proj₁ (ha k hk)) (λ k hk → proj₂ (hb k hk)))
    (Sparse.sectorProduct (C.imagTerms a) (C.realTerms b) (λ k hk → proj₂ (ha k hk)) (λ k hk → proj₁ (hb k hk))) n hn

-- Reopen the whole ramified interval, not only the q-indexed subset.
ramifiedReflect : ∀ a b D0 → R41.SectorC a → R41.SectorC b →
  (∀ n → n ≤ D0 → a (stride n) ≈C b (stride n)) →
  ∀ n → n ≤ stride D0 → a n ≈C b n
ramifiedReflect a b D0 ha hb he n hn with n % 41 NP.≟ zero
... | no h = complexTrans (ha n h) (complexSym (hb n h))
... | yes h = subst (λ k → a k ≈C b k) (sym (Sparse.multiple n h))
  (he (n / 41) (Weld.quotBound n D0 hn))

module At (inputs : Round11.BishopCutset) where
  module W = Weld.At inputs
  module O = Actual.At inputs
  module RN = Red.At inputs

  reflectProduct : ∀ g raw cs gz nz D0 →
    Sector g → R41.SectorC raw → Integral cs →
    PrefixEq (lift gz) (restrict g) D0 →
    (∀ n → n ≤ D0 → R41.restrictC raw n ≈C E.lift (lift nz) n) →
    PrefixEq (lift (Cert.column Cert.j cs)) (restrict (Actual.column cs)) D0 →
    Cert.Through D0 (λ n → I.rowZ gz nz n ≡ Cert.column Cert.j cs n) →
    ∀ n → n ≤ stride D0 → N._⊗c_ (E.lift g) raw n ≈C E.lift (Actual.column cs) n
  reflectProduct g raw cs gz nz D0 sg sr ok hg hr hc gate =
    ramifiedReflect _ _ D0
      (complexSectorProduct (E.lift g) raw (liftSector g sg) sr)
      (liftSector (Actual.column cs) (columnSector cs))
      (λ n hn →
        let a = R41.restrictC raw
            realEq = Ref.bothPrefix (restrict g) (C.realTerms a) (lift gz) (lift nz) n
              (λ k hk → P.≃-symm (hg k (NP.≤-trans hk hn)))
              (λ k hk → proj₁ (hr k (NP.≤-trans hk hn)))
            imagEq = U.convPrefix (restrict g) (C.imagTerms a) H.zeroSeries n
              (λ k hk → proj₂ (hr k (NP.≤-trans hk hn)))
        in complexTrans (R41.reduceComplex (E.lift g) raw (liftSector g sg) n)
          (complexTrans (Red.leftReal (restrict g) a n)
            (P.≃-trans realEq
              (P.≃-trans (P.≃-symm (I.rowEmbed gz nz n))
                (P.≃-trans (I.embedCong (Cert.throughAt D0 gate n hn)) (hc n hn))) ,
             P.≃-trans imagEq (H.zeroRow (restrict g) n))))

  diagonal : W.UnitGate → W.DiagonalGate → ∀ n → n ≤ 3362 →
    O.diagonalNormalized n ≈C E.lift Actual.diagColumn n
  diagonal hu hd = reflectProduct Actual.gDiag O.diagNorm Packet.diagonal
    (Cert.gDiag Cert.j) Cert.nD 82 gDiagSector O.diagOffSector diagIntegral
    (gDiagRead 82 (prefixRestrict (W.jPrefix hu) 82 (from-yes (82 NP.≤? 3322))))
    (W.diagComplex hu hd)
    (columnRead Cert.j 82 Packet.diagonal diagIntegral
      (prefixRestrict (W.jPrefix hu) 82 (from-yes (82 NP.≤? 3322))))
    (proj₂ (proj₂ hd))

  slice : W.UnitGate → W.SliceGate → ∀ n → n ≤ 1722 →
    O.sliceNormalized n ≈C E.lift Actual.sliceColumn n
  slice hu hs = reflectProduct Actual.gSlice O.sliceNorm Packet.slice
    (Cert.gSlice Cert.j) Cert.nS 42 gSliceSector O.sliceOffSector sliceIntegral
    (gSliceRead 42 (prefixRestrict (W.jPrefix hu) 42 (from-yes (42 NP.≤? 3322))))
    (W.sliceComplex hu hs)
    (columnRead Cert.j 42 Packet.slice sliceIntegral
      (prefixRestrict (W.jPrefix hu) 42 (from-yes (42 NP.≤? 3322))))
    (proj₂ (proj₂ hs))

  diagonalZero : W.UnitGate → W.DiagonalGate → ∀ n → n ≤ 3362 → O.diagonalResidual n ≈C A.zeroC
  diagonalZero hu hd n hn = complexTrans (A.subCCongruent (diagonal hu hd n hn) (C.≈C-refl _))
    (Prod.differenceSelf _)

  sliceZero : W.UnitGate → W.SliceGate → ∀ n → n ≤ 1722 → O.sliceResidual n ≈C A.zeroC
  sliceZero hu hs n hn = complexTrans (A.subCCongruent (slice hu hs n hn) (C.≈C-refl _))
    (Prod.differenceSelf _)
