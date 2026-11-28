module DASHI.Moonshine.CM163BishopHecke41FinitePrefixReflectionExact where

-- SOURCE-WRITTEN, kernel pending. Reflect the exact integer residuals
-- into the original real Cauchy row. Finite prefix uniqueness, not a
-- hash of a coefficient array, is the proof transport.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Relation.Nullary using (yes; no)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base as Z using (ℤ; +_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Integer.Solver using (module +-*-Solver)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as Cancel
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionIntegerRowExact as I
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopRamanujanDeltaUnitExact as D
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as Ram
import DASHI.Moonshine.JInvariantBishopEulerDefectUniquenessExact as Pos
import DASHI.Moonshine.CM163BishopHecke41FormalNormEulerExact as Euler
import DASHI.Moonshine.CM163BishopHecke41ReducedNormFlowExact as Reduced
import DASHI.Moonshine.CM163BishopHecke41IntegerPrefixCertificateExact as Cert
import DASHI.Moonshine.CM163BishopHecke41ReducedCauchyExact as R41
import DASHI.Moonshine.CM163BishopHecke41FormalCyclotomicNormExact as N
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open G
open U using (PrefixEq)
open I using (embed; embedCong; embedMul; rowEmbed)

lift : I.SeriesZ → Series
lift f n = embed (f n)

embedSub : ∀ a b → embed (Z._-_ a b) ≃ (embed a - embed b)
embedSub a b = P.≃-trans
  (P.⋆-cong (Q.*≡* (let open +-*-Solver in solve 2
    (λ a b → (a :- b) :* con (+ 1) := (a :* con (+ 1) :- b :* con (+ 1)) :* con (+ 1))
    refl a b)))
  (P.⋆-distrib-to-p⋆-q⋆ (a / 1) (b / 1))

bothPrefix : ∀ a b f g n → PrefixEq a f n → PrefixEq b g n →
  (a ⊗s b) n ≃ (f ⊗s g) n
bothPrefix a b f g n ha hb = P.≃-trans (U.convPrefix a b g n hb)
  (P.≃-trans (Ring.rowComm a g n)
    (P.≃-trans (U.convPrefix g a f n ha) (Ring.rowComm g f n)))

prefixRestrict : ∀ {f g n} → PrefixEq f g n → ∀ m → m ≤ n → PrefixEq f g m
prefixRestrict h m hm k hk = h k (NP.≤-trans hk hm)

prefixRow : ∀ a b f g n → PrefixEq a f n → PrefixEq b g n →
  PrefixEq (a ⊗s b) (f ⊗s g) n
prefixRow a b f g n ha hb k hk = bothPrefix a b f g k
  (prefixRestrict ha k hk) (prefixRestrict hb k hk)

-- Multiplication by a unit is triangular. Reuse the original
-- zero-head Cauchy split, keeping the EXACT lower-degree prefix.
unitPrefixUnique : ∀ a f g → a zero ≃ R.1ℝ → ∀ n →
  PrefixEq (a ⊗s f) (a ⊗s g) n → PrefixEq f g n
unitPrefixUnique a f g a0 zero h zero hk =
  let left = P.≃-trans (Row.cauchyCoefficientZero a f)
        (P.≃-trans (P.*-congʳ a0) (P.*-identityˡ (f zero)))
      right = P.≃-trans (Row.cauchyCoefficientZero a g)
        (P.≃-trans (P.*-congʳ a0) (P.*-identityˡ (g zero)))
  in P.≃-trans (P.≃-symm left) (P.≃-trans (h zero z≤n) right)
unitPrefixUnique a f g a0 zero h (suc k) ()
unitPrefixUnique a f g a0 (suc n) h k hk with k NP.≟ suc n
... | no ne = unitPrefixUnique a f g a0 n (λ i hi → h i (NP.≤-step hi))
  k (NP.≤-pred (NP.≤∧≢⇒< hk ne))
... | yes refl =
  let prior = unitPrefixUnique a f g a0 n (λ i hi → h i (NP.≤-step hi))
      tailF = (Row.shift a ⊗s f) n
      tailG = (Row.shift a ⊗s g) n
      t = U.convPrefix (Row.shift a) f g n prior
      left = P.≃-trans (Row.cauchyCoefficientSuccessor a f n)
        (P.+-cong (P.≃-trans (P.*-congʳ a0) (P.*-identityˡ (f (suc n)))) P.≃-refl)
      right = P.≃-trans (Row.cauchyCoefficientSuccessor a g n)
        (P.+-cong (P.≃-trans (P.*-congʳ a0) (P.*-identityˡ (g (suc n)))) (P.≃-symm t))
      eq = P.≃-trans (P.≃-symm left) (P.≃-trans (h (suc n) NP.≤-refl) right)
  in P.≃-trans (let open P.ℝ-Solver in solve 2 (λ x t → x ⊜ (x ⊕ t) ⊖ t)
      P.≃-refl (f (suc n)) tailF)
    (P.≃-trans (P.+-congʳ eq)
      (let open P.ℝ-Solver in solve 2 (λ x t → (x ⊕ t) ⊖ t ⊜ x)
        P.≃-refl (g (suc n)) tailF))

-- Finite Euler uniqueness uses the positive degree n, not an
-- analytic uniqueness or unbounded recurrence assumption.
eulerPrefixUnique : ∀ a f g → a zero ≃ R.0ℝ → f zero ≃ g zero →
  ∀ n → PrefixEq (F.δ f) (a ⊗s f) n →
  PrefixEq (F.δ g) (a ⊗s g) n → PrefixEq f g n
eulerPrefixUnique a f g a0 h0 zero hf hg zero hk = h0
eulerPrefixUnique a f g a0 h0 zero hf hg (suc k) ()
eulerPrefixUnique a f g a0 h0 (suc n) hf hg k hk with k NP.≟ suc n
... | no ne = eulerPrefixUnique a f g a0 h0 n
  (λ i hi → hf i (NP.≤-step hi)) (λ i hi → hg i (NP.≤-step hi))
  k (NP.≤-pred (NP.≤∧≢⇒< hk ne))
... | yes refl =
  let prior = eulerPrefixUnique a f g a0 h0 n
        (λ i hi → hf i (NP.≤-step hi)) (λ i hi → hg i (NP.≤-step hi))
      read = P.≃-trans (P.≃-symm (U.D1Meaning f (suc n)))
        (P.≃-trans (hf (suc n) NP.≤-refl)
          (P.≃-trans (U.zeroHead a f a0 n)
            (P.≃-trans (U.convPrefix (Row.shift a) f g n prior)
              (P.≃-trans (P.≃-symm (U.zeroHead a g a0 n))
                (P.≃-trans (P.≃-symm (hg (suc n) NP.≤-refl))
                  (U.D1Meaning g (suc n)))))))
  in Cancel.cancelLeft (NR.natReal (suc n)) (Pos.positiveNat n) read

rowReflect : ∀ a b f g n → PrefixEq (lift a) f n → PrefixEq (lift b) g n →
  embed (I.rowZ a b n) ≃ (f ⊗s g) n
rowReflect a b f g n ha hb = P.≃-trans (rowEmbed a b n)
  (bothPrefix (lift a) (lift b) f g n ha hb)

X3Read : lift Cert.X3 ≈s U.X3
X3Read n = P.≃-trans (rowEmbed (I.rowZ Cert.X Cert.X) Cert.X n)
  (mulCong (λ k → P.≃-trans (rowEmbed Cert.X Cert.X k)
    (mulCong Ram.actualX Ram.actualX k)) Ram.actualX n)

Y2Read : lift Cert.Y2 ≈s U.Y2
Y2Read n = P.≃-trans (rowEmbed Cert.Y Cert.Y n) (mulCong Ram.actualY Ram.actualY n)

discRead : lift Cert.disc ≈s U.disc
discRead n = P.≃-trans (embedSub (Cert.X3 n) (Cert.Y2 n))
  (subCong X3Read Y2Read n)

unitRead : ∀ D0 u j → Cert.UnitGate D0 u j → PrefixEq (lift u) D.unit D0
unitRead D0 u j gate n hn =
  let eq = Cert.throughAt D0 (proj₁ gate) n hn
      read = P.≃-trans (P.≃-symm (embedMul (+ 1728) (u n)))
        (P.≃-trans (embedCong eq) (discRead (suc n)))
      finish = let open P.ℝ-Solver in solve 1
        (λ x → x ⊜ Κ (+ 1728 / 1) ⊗ (Κ (+ 1 / 1728) ⊗ x))
        P.≃-refl (U.disc (suc n))
  in Cancel.cancelLeft (NR.natReal 1728) (Pos.positiveNat 1727)
      (P.≃-trans read finish)

jRead : ∀ D0 u j → Cert.UnitGate D0 u j → PrefixEq (lift j) D.Junit D0
jRead D0 u j gate =
  unitPrefixUnique D.unit (lift j) D.Junit D.unit0 D0
    (λ n hn →
      P.≃-trans (P.≃-symm (rowReflect u j D.unit (lift j) n
        (prefixRestrict (unitRead D0 u j gate) n hn) (λ _ _ → P.≃-refl)))
        (P.≃-trans (embedCong (Cert.throughAt D0 (proj₂ gate) n hn))
          (P.≃-trans (X3Read n) (P.≃-symm (D.jRelation n)))))

-- Given the literal h-prefix, reflect the integer H*L=D H
-- residual into the actual native logarithmic derivative. There is
-- no need to reflect a separately generated formal inverse.
logRead : ∀ h h0 hz l M →
  PrefixEq (lift hz) h M →
  Cert.Through M (λ n → I.rowZ hz l n ≡ Z._*_ (+ n) (hz n)) →
  PrefixEq (lift l) (Euler.Log.ell h h0) M
logRead h h0 hz l M hh gate =
  unitPrefixUnique h (lift l) (Euler.Log.ell h h0) h0 M (λ n hn →
    P.≃-trans (P.≃-symm (rowReflect hz l h (lift l) n
      (prefixRestrict hh n hn) (λ _ _ → P.≃-refl)))
      (P.≃-trans (embedCong (Cert.throughAt M gate n hn))
        (P.≃-trans (embedMul (+ n) (hz n))
          (P.≃-trans (P.*-congˡ (hh n hn))
            (P.≃-trans (P.≃-symm (U.D1Meaning h n))
              (P.≃-trans (Euler.Log.flow h h0 n)
                (Ring.rowComm (Euler.Log.ell h h0) h n)))))))

module At (inputs : Round11.BishopCutset) where
  module Red = Reduced.At inputs

  module For (h : Series) (h0 : h zero ≃ R.1ℝ) where
    module A = Red.For h h0

    normRead : ∀ D0 l a →
      PrefixEq (lift l) A.driver D0 →
      a zero ≡ (+ 1) →
      Cert.Through D0 (λ n → I.rowZ l a n ≡ Z._*_ (+ n) (a n)) →
      PrefixEq (lift a) A.real D0
    normRead D0 l a hl a0 gate =
      eulerPrefixUnique A.driver (lift a) A.real A.driver0
        (P.≃-trans (embedCong a0) (P.≃-symm (proj₁ A.zeroMode))) D0
        (λ n hn →
          P.≃-trans (U.D1Meaning (lift a) n)
            (P.≃-trans (P.≃-symm (embedMul (+ n) (a n)))
              (P.≃-trans (embedCong (symEq (Cert.throughAt D0 gate n hn)))
                (rowReflect l a A.driver (lift a) n
                  (prefixRestrict hl n hn) (λ _ _ → P.≃-refl)))))
        (λ n hn → A.realFlow n)
      where
      symEq : ∀ {X : Set} {x y : X} → x ≡ y → y ≡ x
      symEq refl = refl

    complexNormRead : ∀ D0 l a →
      PrefixEq (lift l) A.driver D0 →
      a zero ≡ (+ 1) →
      Cert.Through D0 (λ n → I.rowZ l a n ≡ Z._*_ (+ n) (a n)) →
      ∀ n → n ≤ D0 → C._≈C_ (A.reduced n) (Euler.lift (lift a) n)
    complexNormRead D0 l a hl a0 gate n hn =
      P.≃-symm (normRead D0 l a hl a0 gate n hn) , A.imagZero n
