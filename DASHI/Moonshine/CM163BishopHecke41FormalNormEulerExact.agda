module DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact where

-- SOURCE-WRITTEN, kernel pending. Euler derivative of the actual
-- cyclic Cauchy norm, from the original real coefficient ring and
-- literal inverse. No analytic logarithm and no complex root choice.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat.DivMod using (_%_)
open import Data.Nat.Properties as NP using (*-comm)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Rational.Unnormalised using (0ℚᵘ; 1ℚᵘ)
import Real as R
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexCommutativeSemiringLawsExact as L
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopFormalCompositionFlowExact as Flow
import DASHI.Moonshine.JInvariantBishopFormalGeometricInverseExact as Inv
import DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact as H
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Moonshine.CM163BishopHecke41RamifiedPhaseExact as Ram
import DASHI.Moonshine.CM163BishopHecke41SectorFilterExact as Filter
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open N
open C using (BishopComplex; _≈C_)
open A using (_*C_; _+C_; powC)
open Comp using (complexTrans; complexSym)

lift : G.Series → SeriesC
lift f n = C.complex (f n) R.0ℝ

liftCong : ∀ {f g} → G._≈s_ f g → lift f ≈cs lift g
liftCong h n = h n , P.≃-refl

infixl 6 _⊕c_
_⊕c_ : SeriesC → SeriesC → SeriesC
(f ⊕c g) n = f n +C g n

zeroC : SeriesC
zeroC = λ _ → A.zeroC

δ : SeriesC → SeriesC
δ f n = C.complex (F.δ (C.realTerms f) n) (F.δ (C.imagTerms f) n)

dCong : ∀ {f g} → f ≈cs g → δ f ≈cs δ g
dCong h n = P.*-congˡ (proj₁ (h n)) , P.*-congˡ (proj₂ (h n))

addCong : ∀ {a b c d} → a ≈cs b → c ≈cs d → (a ⊕c c) ≈cs (b ⊕c d)
addCong h k n = A.addCCongruent (h n) (k n)

dUnit : δ unit ≈cs zeroC
dUnit n = Flow.dUnit n , Flow.dZero n

liftMul : ∀ f g → (lift f ⊗c lift g) ≈cs lift (G._⊗s_ f g)
liftMul f g n =
  (let open G.Solver in solve 2 (λ f g → f ⊗ g ⊖ Κ 0ℚᵘ ⊗ Κ 0ℚᵘ ⊜ f ⊗ g)
    G.reflS f g n) ,
  (let open G.Solver in solve 2 (λ f g → f ⊗ Κ 0ℚᵘ ⊕ Κ 0ℚᵘ ⊗ g ⊜ Κ 0ℚᵘ)
    G.reflS f g n)

liftD : ∀ f → δ (lift f) ≈cs lift (F.δ f)
liftD f n = P.≃-refl , Flow.dZero n

dMul : ∀ f g → δ (f ⊗c g) ≈cs ((δ f ⊗c g) ⊕c (f ⊗c δ g))
dMul f g n =
  let a = C.realTerms f; b = C.imagTerms f; c = C.realTerms g; d = C.imagTerms g
      open G
  in
  (transS (F.dSub (a ⊗s c) (b ⊗s d))
    (transS (G.subCong (F.dMul a c) (F.dMul b d))
      (let open G.Solver in solve 8
        (λ a b c d da db dc dd →
          (da ⊗ c ⊕ a ⊗ dc) ⊖ (db ⊗ d ⊕ b ⊗ dd)
          ⊜ (da ⊗ c ⊖ db ⊗ d) ⊕ (a ⊗ dc ⊖ b ⊗ dd))
        reflS a b c d (F.δ a) (F.δ b) (F.δ c) (F.δ d)))) n ,
  (transS (F.dAdd (a ⊗s d) (b ⊗s c))
    (transS (G.addCong (F.dMul a d) (F.dMul b c))
      (let open G.Solver in solve 8
        (λ a b c d da db dc dd →
          (da ⊗ d ⊕ a ⊗ dd) ⊕ (db ⊗ c ⊕ b ⊗ dc)
          ⊜ (da ⊗ d ⊕ db ⊗ c) ⊕ (a ⊗ dd ⊕ b ⊗ dc))
        reflS a b c d (F.δ a) (F.δ b) (F.δ c) (F.δ d)))) n

dTwist : ∀ w f → δ (twist w f) ≈cs twist w (δ f)
dTwist w f n =
  let a = C.re (f n); b = C.im (f n)
      x = C.re (powC w n); y = C.im (powC w n)
      k = R.pow (NR.natReal n) 1
  in (let open P.ℝ-Solver in solve 5
        (λ k a b x y → k ⊗ (a ⊗ x ⊖ b ⊗ y) ⊜ (k ⊗ a) ⊗ x ⊖ (k ⊗ b) ⊗ y)
        P.≃-refl k a b x y) ,
     (let open P.ℝ-Solver in solve 5
        (λ k a b x y → k ⊗ (a ⊗ y ⊕ b ⊗ x) ⊜ (k ⊗ a) ⊗ y ⊕ (k ⊗ b) ⊗ x)
        P.≃-refl k a b x y)

mulZeroLeft : ∀ f → (zeroC ⊗c f) ≈cs zeroC
mulZeroLeft f n =
  (let open G.Solver in solve 2 (λ a b → Κ 0ℚᵘ ⊗ a ⊖ Κ 0ℚᵘ ⊗ b ⊜ Κ 0ℚᵘ)
    G.reflS (C.realTerms f) (C.imagTerms f) n) ,
  (let open G.Solver in solve 2 (λ a b → Κ 0ℚᵘ ⊗ b ⊕ Κ 0ℚᵘ ⊗ a ⊜ Κ 0ℚᵘ)
    G.reflS (C.realTerms f) (C.imagTerms f) n)

mulAddRight : ∀ a b c → ((a ⊕c b) ⊗c c) ≈cs ((a ⊗c c) ⊕c (b ⊗c c))
mulAddRight a b c n =
  let ar = C.realTerms a; ai = C.imagTerms a; br = C.realTerms b; bi = C.imagTerms b
      cr = C.realTerms c; ci = C.imagTerms c
  in (let open G.Solver in solve 6 (λ ar ai br bi cr ci →
        (ar ⊕ br) ⊗ cr ⊖ (ai ⊕ bi) ⊗ ci
        ⊜ (ar ⊗ cr ⊖ ai ⊗ ci) ⊕ (br ⊗ cr ⊖ bi ⊗ ci))
        G.reflS ar ai br bi cr ci n) ,
     (let open G.Solver in solve 6 (λ ar ai br bi cr ci →
        (ar ⊕ br) ⊗ ci ⊕ (ai ⊕ bi) ⊗ cr
        ⊜ (ar ⊗ ci ⊕ ai ⊗ cr) ⊕ (br ⊗ ci ⊕ bi ⊗ cr))
        G.reflS ar ai br bi cr ci n)

-- Real formal logarithmic derivative via the already-owned geometric
-- inverse. No log function needs to exist at a complex point.
module Log (h : G.Series) (h0 : R._≃_ (h zero) R.1ℝ) where
  open G
  b = H.unitSeries ⊖s h
  b0 : R._≃_ (b zero) R.0ℝ
  b0 = P.≃-trans (P.+-cong P.≃-refl (P.-‿cong h0)) (P.+-inverseʳ R.1ℝ)
  v = Inv.geometric b
  hv : (h ⊗s v) ≈s H.unitSeries
  hv = transS (G.mulCong (let open G.Solver in solve 1
    (λ h → h ⊜ Κ 1ℚᵘ ⊖ (Κ 1ℚᵘ ⊖ h)) reflS h) reflS)
    (Inv.inverseFromZeroMode b b0)
  ell : Series
  ell = F.δ h ⊗s v
  flow : F.δ h ≈s (ell ⊗s h)
  flow = symS (transS (let open G.Solver in solve 3
    (λ dh v h → (dh ⊗ v) ⊗ h ⊜ dh ⊗ (h ⊗ v)) reflS (F.δ h) v h)
    (transS (G.mulCong reflS hv) (Ring.rowUnitRight (F.δ h))))

module At (inputs : Round11.BishopCutset) where
  module Norm = N.At inputs
  open Norm using (factor; normFrom; norm; zeta)

  traceFrom : SeriesC → Nat → Nat → SeriesC
  traceFrom ell k zero = zeroC
  traceFrom ell k (suc n) = factor ell k ⊕c traceFrom ell (suc k) n

  factorFlow : ∀ h ell → δ h ≈cs (ell ⊗c h) →
    ∀ k → δ (factor h k) ≈cs (factor ell k ⊗c factor h k)
  factorFlow h ell he k =
    transCs (dTwist (powC zeta k) h)
      (transCs (twistCong (powC zeta k) he)
        (symCs (twistMul (powC zeta k) ell h)))

  normFlow : ∀ h ell → δ h ≈cs (ell ⊗c h) →
    ∀ k n → δ (normFrom h k n) ≈cs (traceFrom ell k n ⊗c normFrom h k n)
  normFlow h ell he k zero = transCs dUnit (symCs (mulZeroLeft unit))
  normFlow h ell he k (suc n) =
    let a = factor h k
        e = factor ell k
        b = normFrom h (suc k) n
        v = traceFrom ell (suc k) n
        swap = transCs (symCs (mulAssoc a v b))
          (transCs (mulCong (mulComm a v) reflCs) (mulAssoc v a b))
    in transCs (dMul a b)
      (transCs (addCong (mulCong (factorFlow h ell he k) reflCs)
        (mulCong reflCs (normFlow h ell he (suc k) n)))
        (transCs (addCong (mulAssoc e a b) swap)
          (symCs (mulAddRight e v (a ⊗c b)))))

  actualNormFlow : ∀ h h0 →
    δ (norm (lift h)) ≈cs
      (traceFrom (lift (Log.ell h h0)) zero 41 ⊗c norm (lift h))
  actualNormFlow h h0 = normFlow (lift h) (lift (Log.ell h h0))
    (transCs (liftD h) (transCs (liftCong (Log.flow h h0))
      (symCs (liftMul (Log.ell h h0) h)))) zero 41

  -- Finite trace at the actual coefficient, using exact powers rather
  -- than a separate root-of-unity summation hypothesis.
  factorPower : ∀ f k m → factor f k m ≈C (f m *C powC (powC zeta m) k)
  factorPower f k m = A.mulCCongruent (C.≈C-refl _)
    (complexTrans (Ram.powPow zeta k m)
      (complexTrans (Filter.powIndex zeta (*-comm m k))
        (complexSym (Ram.powPow zeta m k))))

  traceRead : ∀ f k n m → traceFrom f k n m ≈C
    (f m *C (powC (powC zeta m) k *C Filter.geometric (powC zeta m) n))
  traceRead f k zero m =
    complexSym (complexTrans (A.mulCCongruent (C.≈C-refl _)
      (L.complexMultiplyRightZero _)) (L.complexMultiplyRightZero _))
  traceRead f k (suc n) m =
    let z = powC zeta m
        p = powC z k
        g = Filter.geometric z n
        x = f m
        read = complexTrans (L.complexMultiplyDistributesLeft p A.oneC (z *C g))
          (A.addCCongruent (L.complexMultiplyRightIdentity p)
            (complexTrans (complexSym (L.complexMultiplyAssociative p z g))
              (A.mulCCongruent (L.complexMultiplyCommutative p z) (C.≈C-refl _))))
    in complexTrans (A.addCCongruent (factorPower f k m) (traceRead f (suc k) n m))
      (complexTrans (complexSym (L.complexMultiplyDistributesLeft x p (powC z (suc k) *C g)))
        (A.mulCCongruent (C.≈C-refl _) (complexSym read)))

  traceAt : ∀ f m → traceFrom f zero 41 m ≈C
    (f m *C Filter.geometric (powC zeta m) 41)
  traceAt f m = complexTrans (traceRead f zero 41 m)
    (A.mulCCongruent (C.≈C-refl _) (L.complexMultiplyLeftIdentity _))

  traceOffSector : ∀ f m → (m % 41 ≡ zero → ⊥) → traceFrom f zero 41 m ≈C A.zeroC
  traceOffSector f m hn = complexTrans (traceAt f m)
    (complexTrans (A.mulCCongruent (C.≈C-refl _) (Norm.S.rootTraceZero m hn))
      (L.complexMultiplyRightZero _))
