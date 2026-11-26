module DASHI.Moonshine.JInvariantBishopHyperQOriginalCoefficientsExact where

-- SOURCE-WRITTEN, UNCOMPILED. Actual finite coefficient construction
-- for the normalized binomial root and original hypergeometric
-- composition. Every output coefficient is a finite sum. The
-- all-index identities and analytic evaluation are distinct producers.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (_<_; _≤_; z≤n; s≤s)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact as Raw
import DASHI.Foundations.BishopChudnovskyNativeFactorialEulerAttachmentExact as A
import DASHI.Foundations.BishopChudnovskyNativeHyperODEExact as Hyper
open import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact
  using (Series; _⊕s_; _⊖s_; _⊗s_; scale; D; X; Y; X3; disc;
         sub0; right0; mul0; convPrefix; Solution; allCoefficientsUnique;
         squareEuler; disc0)

zeroSeries unitSeries : Series
zeroSeries n = R.0ℝ
unitSeries zero = R.1ℝ
unitSeries (suc n) = R.0ℝ

power : Series → Nat → Series
power a zero = unitSeries
power a (suc k) = a ⊗s power a k

zeroRow : (a : Series) (n : Nat) → (a ⊗s zeroSeries) n ≃ R.0ℝ
zeroRow a zero = P.≃-trans (C.cauchyCoefficientZero a zeroSeries)
  (P.*-zeroʳ (a zero))
zeroRow a (suc n) = P.≃-trans (C.cauchyCoefficientSuccessor a zeroSeries n)
  (P.≃-trans (P.+-cong (P.*-zeroʳ (a zero)) (zeroRow (C.shift a) n))
    (P.+-identityʳ R.0ℝ))

-- If the inner series has zero constant term, its kth power has
-- no coefficients below k. This is the finite-support justification
-- for composing by a sum over k <= n; no analytic limit is used.
powerBelow : (a : Series) → a zero ≃ R.0ℝ →
  (k n : Nat) → n < k → power a k n ≃ R.0ℝ
powerBelow a az zero n ()
powerBelow a az (suc k) zero h =
  P.≃-trans (C.cauchyCoefficientZero a (power a k))
    (P.≃-trans (P.*-congʳ az) (P.*-zeroˡ (power a k zero)))
powerBelow a az (suc k) (suc n) h =
  P.≃-trans (C.cauchyCoefficientSuccessor a (power a k) n)
    (P.≃-trans
      (P.+-cong
        (P.≃-trans (P.*-congʳ az) (P.*-zeroˡ (power a k (suc n))))
        (P.≃-trans
          (convPrefix (C.shift a) (power a k) zeroSeries n
            (λ j hj → powerBelow a az k j (NP.≤-<-trans hj (NP.≤-pred h))))
          (zeroRow (C.shift a) n)))
      (P.+-identityʳ R.0ℝ))

compose : Series → Series → Series
compose outer inner n = R.∑₀
  (λ k → outer k * power inner k n) (suc n)

composeZero : (outer inner : Series) → compose outer inner zero ≃ outer zero
composeZero outer inner = P.≃-trans
  (P.+-cong P.≃-refl (P.*-identityʳ (outer zero)))
  (P.+-identityˡ (outer zero))

-- Actual z(q) = (X^3-Y^2)/X^3. The reciprocal candidate is the
-- finite formal geometric expansion around the cusp unit.
minusX3Tail : Series
minusX3Tail = scale (R.- R.1ℝ) (X3 ⊖s unitSeries)

inverseX3 : Series
inverseX3 = compose (λ _ → R.1ℝ) minusX3Tail

Zcoord : Series
Zcoord = disc ⊗s inverseX3

zCoordZero : Zcoord zero ≃ R.0ℝ
zCoordZero =
  P.≃-trans (C.cauchyCoefficientZero disc inverseX3)
    (P.≃-trans (P.*-congʳ
      disc0)
      (P.*-zeroˡ (inverseX3 zero)))

zPowerBelow : (k n : Nat) → n < k → power Zcoord k n ≃ R.0ℝ
zPowerBelow = powerBelow Zcoord zCoordZero

-- The actual normalized binomial branch, expanded formally at X(0)=1.
halfRatio : Nat → Q.ℚᵘ
halfRatio n = Raw.frac
  (Z._-_ (+ 1) (+ (Nat._*_ 2 n))) (Nat._*_ 2 (suc n))
  (NP.m*n≢0 2 (suc n))

halfCoeff : Series
halfCoeff zero = R.1ℝ
halfCoeff (suc n) = (halfRatio n ⋆) * halfCoeff n

rootCandidate : Series
rootCandidate = compose halfCoeff (X ⊖s unitSeries)

rootConstant : rootCandidate zero ≃ R.1ℝ
rootConstant = composeZero halfCoeff (X ⊖s unitSeries)

-- Positive hypergeometric coefficient from the ORIGINAL signed
-- factorial term by undoing its exact nonzero CM argument z0.
-- Do not use an independent factorial recurrence or a new sign source.
invZ : ℝ
invZ = ((Z.-_ (+ 262537412640768000)) / 1728) ⋆

invZPower : (n : Nat) →
  (R.pow invZ n * R.pow Hyper.z n) ≃ R.1ℝ
invZPower zero = P.*-identityˡ R.1ℝ
invZPower (suc n) =
  P.≃-trans
    (let open P.ℝ-Solver in solve 4 (λ a b c d →
      (a ⊗ c) ⊗ (b ⊗ d) ⊜ (a ⊗ b) ⊗ (c ⊗ d))
      P.≃-refl (R.pow invZ n) (R.pow Hyper.z n) invZ Hyper.z)
    (P.≃-trans (P.*-cong (invZPower n)
      (let open P.ℝ-Solver in solve 0
        (Κ ((Z.-_ (+ 262537412640768000)) / 1728) ⊗ Κ Hyper.zQ
          ⊜ Κ Q.1ℚᵘ) P.≃-refl))
      (P.*-identityˡ R.1ℝ))

hyperCoeff : Series
hyperCoeff n = R.pow invZ n * A.hTerm n

hyperCoeffAtCM : (n : Nat) →
  (hyperCoeff n * R.pow Hyper.z n) ≃ A.hTerm n
hyperCoeffAtCM n =
  P.≃-trans
    (let open P.ℝ-Solver in solve 3 (λ a b c →
      (a ⊗ b) ⊗ c ⊜ (a ⊗ c) ⊗ b)
      P.≃-refl (R.pow invZ n) (A.hTerm n) (R.pow Hyper.z n))
    (P.≃-trans (P.*-congʳ (invZPower n)) (P.*-identityˡ (A.hTerm n)))

hyperJetCoeff : Series
hyperJetCoeff n = NR.natReal n * hyperCoeff n

hyperCandidate hyperJetCandidate : Series
hyperCandidate = compose hyperCoeff Zcoord
hyperJetCandidate = compose hyperJetCoeff Zcoord

hyperConstant : hyperCandidate zero ≃ R.1ℝ
hyperConstant = P.≃-trans (composeZero hyperCoeff Zcoord)
  (P.≃-trans (P.*-identityˡ (A.hTerm zero)) P.≃-refl)

jetConstant : hyperJetCandidate zero ≃ R.0ℝ
jetConstant = P.≃-trans (composeZero hyperJetCoeff Zcoord)
  (P.*-zeroˡ (hyperCoeff zero))

-- The universal uniqueness theorem now consumes THESE literal
-- candidates, not arbitrary f/g. The two residual proofs and the
-- binomial square theorem are still actual mathematical producers.
rootHyperSame :
  Solution rootCandidate → Solution hyperCandidate →
  (n : Nat) → rootCandidate n ≃ hyperCandidate n
rootHyperSame hr hh =
  allCoefficientsUnique rootCandidate hyperCandidate hr hh
    (P.≃-trans rootConstant (P.≃-symm hyperConstant))

convBoth : (a b f g : Series) →
  ((n : Nat) → a n ≃ f n) → ((n : Nat) → b n ≃ g n) →
  (n : Nat) → (a ⊗s b) n ≃ (f ⊗s g) n
convBoth a b f g ha hb n =
  C.BishopSum.sum-cong-≋
    (λ i → P.*-cong (ha (toℕ i))
      (hb (n Nat.∸ toℕ i)))

formalHyperSquare :
  Solution rootCandidate → Solution hyperCandidate →
  ((n : Nat) → (rootCandidate ⊗s rootCandidate) n ≃ X n) →
  (n : Nat) → (hyperCandidate ⊗s hyperCandidate) n ≃ X n
formalHyperSquare hr hh hs n =
  P.≃-trans
    (convBoth hyperCandidate hyperCandidate rootCandidate rootCandidate
      (λ k → P.≃-symm (rootHyperSame hr hh k))
      (λ k → P.≃-symm (rootHyperSame hr hh k)) n)
    (hs n)

formalHyperSquareJet :
  Solution rootCandidate → Solution hyperCandidate →
  ((n : Nat) → (rootCandidate ⊗s rootCandidate) n ≃ X n) →
  (n : Nat) →
  ((D 1 hyperCandidate ⊗s hyperCandidate) ⊕s
    (hyperCandidate ⊗s D 1 hyperCandidate)) n ≃ D 1 X n
formalHyperSquareJet hr hh hs = squareEuler hyperCandidate (formalHyperSquare hr hh hs)
