module DASHI.Physics.Closure.NSTriadKNHHGoodCompactAnnularScalarCutoffRound68Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND 68 / CONCRETE COMPACT ANNULAR SCALAR CUTOFF
--
-- Turn the Round67 degree-nine transition into an actual compact annular
-- cutoff rather than leaving it as a local polynomial core.
--
-- First clamp S to a global step H4:
--
--   H4(t)=0       for t<=0,
--        =S(t)    for 0<=t<=1,
--        =1       for 1<=t.
--
-- Since S and its first four derivatives have the matching endpoint jets,
-- this is the canonical C4 gluing pattern.  Then define, in a squared-radius
-- coordinate rho,
--
--   phi(rho) = H4(rho-1) H4(4-rho).
--
-- It is exactly zero for rho<=1 and rho>=4, equals one on 2<=rho<=3, and is
-- between zero and one everywhere.  The squared-radius choice avoids a square
-- root when this scalar cutoff is composed with |xi|^2 in the continuum
-- multiplier.
--
-- This file proves the support/amplitude/plateau facts over exact rationals.
-- The companion polynomial jet theorem already supplies the four matching
-- boundary derivatives; the remaining E theorem is the continuum chain-rule
-- realization after composing rho=|xi|^2 and the physical strain matrix.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥-elim)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; -_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; trans)
open import Relation.Nullary.Decidable.Core using (yes; no)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularPolynomialCoreRound67Exact as C4
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularD1UniformBoundRound68Exact as D1
import DASHI.Physics.Closure.NSTriadKNHHGoodC4AnnularAmplitudeBoundRound68Exact as Amp

four : ℚ
four = Int.+ 4 / 1

three : ℚ
three = Int.+ 3 / 1

two : ℚ
two = Int.+ 2 / 1

zeroBelowOne : 0ℚ ≤ 1ℚ
zeroBelowOne = ℚP.<⇒≤ (ℚP.positive⁻¹ 1ℚ)

clampedStep4 : ℚ → ℚ
clampedStep4 t with 0ℚ ≤? t
... | no _ = 0ℚ
... | yes 0≤t with t ≤? 1ℚ
...   | yes t≤1 = C4.smoothStep4 t
...   | no _ = 1ℚ

clampedStep4OnUnitInterval : ∀ {t} → 0ℚ ≤ t → t ≤ 1ℚ →
  clampedStep4 t ≡ C4.smoothStep4 t
clampedStep4OnUnitInterval {t} 0≤t t≤1 with 0ℚ ≤? t
... | no not0≤t = ⊥-elim (not0≤t 0≤t)
... | yes _ with t ≤? 1ℚ
...   | no nott≤1 = ⊥-elim (nott≤1 t≤1)
...   | yes _ = refl

clampedStep4BelowZero : ∀ {t} → t ≤ 0ℚ → clampedStep4 t ≡ 0ℚ
clampedStep4BelowZero {t} t≤0 with 0ℚ ≤? t
... | no _ = refl
... | yes 0≤t with t ≤? 1ℚ
...   | yes _ =
      let t≡0 = ℚP.≤-antisym t≤0 0≤t
      in trans (cong C4.smoothStep4 t≡0) C4.smoothStep4AtZero
...   | no nott≤1 =
      let t≤1 = ℚP.≤-trans t≤0 zeroBelowOne
      in ⊥-elim (nott≤1 t≤1)

clampedStep4AboveOne : ∀ {t} → 1ℚ ≤ t → clampedStep4 t ≡ 1ℚ
clampedStep4AboveOne {t} 1≤t with 0ℚ ≤? t
... | no not0≤t =
      ⊥-elim (not0≤t (ℚP.≤-trans zeroBelowOne 1≤t))
... | yes _ with t ≤? 1ℚ
...   | no _ = refl
...   | yes t≤1 =
      let t≡1 = ℚP.≤-antisym t≤1 1≤t
      in trans (cong C4.smoothStep4 t≡1) C4.smoothStep4AtOne

clampedStep4Nonnegative : ∀ t → 0ℚ ≤ clampedStep4 t
clampedStep4Nonnegative t with 0ℚ ≤? t
... | no _ = ℚP.≤-refl
... | yes 0≤t with t ≤? 1ℚ
...   | no _ = zeroBelowOne
...   | yes t≤1 = Amp.smoothStep4Nonnegative (0≤t , t≤1)

clampedStep4BelowOne : ∀ t → clampedStep4 t ≤ 1ℚ
clampedStep4BelowOne t with 0ℚ ≤? t
... | no _ = zeroBelowOne
... | yes 0≤t with t ≤? 1ℚ
...   | no _ = ℚP.≤-refl
...   | yes t≤1 = Amp.smoothStep4BelowOne (0≤t , t≤1)

compactAnnularScalarCutoff : ℚ → ℚ
compactAnnularScalarCutoff rho =
  clampedStep4 (rho - 1ℚ) * clampedStep4 (four - rho)

compactAnnularCutoffNonnegative : ∀ rho →
  0ℚ ≤ compactAnnularScalarCutoff rho
compactAnnularCutoffNonnegative rho =
  let
    leftNN = clampedStep4Nonnegative (rho - 1ℚ)
    rightNN = clampedStep4Nonnegative (four - rho)
    instance
      leftNNI = nonNegative leftNN
      rightNNI = nonNegative rightNN
      productNNI = ℚP.nonNeg*nonNeg⇒nonNeg
        (clampedStep4 (rho - 1ℚ)) (clampedStep4 (four - rho))
  in ℚP.nonNegative⁻¹ (compactAnnularScalarCutoff rho)

compactAnnularCutoffBelowOne : ∀ rho →
  compactAnnularScalarCutoff rho ≤ 1ℚ
compactAnnularCutoffBelowOne rho =
  let
    leftNN = clampedStep4Nonnegative (rho - 1ℚ)
    rightNN = clampedStep4Nonnegative (four - rho)
    left≤1 = clampedStep4BelowOne (rho - 1ℚ)
    right≤1 = clampedStep4BelowOne (four - rho)
    first :
      clampedStep4 (rho - 1ℚ) * clampedStep4 (four - rho)
      ≤ 1ℚ * 1ℚ
    first = L2.nonnegativeProductMonotone
      leftNN rightNN zeroBelowOne zeroBelowOne left≤1 right≤1
  in
  subst (compactAnnularScalarCutoff rho ≤_) (ℚP.*-identityˡ 1ℚ) first

compactAnnularCutoffBelowInnerSupport : ∀ {rho} → rho ≤ 1ℚ →
  compactAnnularScalarCutoff rho ≡ 0ℚ
compactAnnularCutoffBelowInnerSupport {rho} rho≤1 =
  let
    shiftedRaw : rho + (- 1ℚ) ≤ 1ℚ + (- 1ℚ)
    shiftedRaw = ℚP.+-monoʳ-≤ (- 1ℚ) rho≤1
    shifted : rho - 1ℚ ≤ 0ℚ
    shifted = subst₂ _≤_ (solve (rho ∷ [])) (solve []) shiftedRaw
      where
      open import Relation.Binary.PropositionalEquality using (subst₂)
  in
  trans
    (cong (λ left → left * clampedStep4 (four - rho))
      (clampedStep4BelowZero shifted))
    (ℚP.*-zeroˡ (clampedStep4 (four - rho)))

compactAnnularCutoffAboveOuterSupport : ∀ {rho} → four ≤ rho →
  compactAnnularScalarCutoff rho ≡ 0ℚ
compactAnnularCutoffAboveOuterSupport {rho} four≤rho =
  let
    shiftedRaw : four + (- rho) ≤ rho + (- rho)
    shiftedRaw = ℚP.+-monoʳ-≤ (- rho) four≤rho
    shifted : four - rho ≤ 0ℚ
    shifted = subst₂ _≤_ (solve (rho ∷ [])) (solve (rho ∷ [])) shiftedRaw
      where
      open import Relation.Binary.PropositionalEquality using (subst₂)
  in
  trans
    (cong (clampedStep4 (rho - 1ℚ) *_)
      (clampedStep4BelowZero shifted))
    (ℚP.*-zeroʳ (clampedStep4 (rho - 1ℚ)))

compactAnnularCutoffPlateau : ∀ {rho} → two ≤ rho → rho ≤ three →
  compactAnnularScalarCutoff rho ≡ 1ℚ
compactAnnularCutoffPlateau {rho} two≤rho rho≤three =
  let
    innerRaw : two + (- 1ℚ) ≤ rho + (- 1ℚ)
    innerRaw = ℚP.+-monoʳ-≤ (- 1ℚ) two≤rho
    inner : 1ℚ ≤ rho - 1ℚ
    inner = subst₂ _≤_ (solve []) (solve (rho ∷ [])) innerRaw
      where
      open import Relation.Binary.PropositionalEquality using (subst₂)

    negated : - three ≤ - rho
    negated = ℚP.neg-antimono-≤ rho≤three
    outerRaw : four + (- three) ≤ four + (- rho)
    outerRaw = ℚP.+-monoˡ-≤ four negated
    outer : 1ℚ ≤ four - rho
    outer = subst₂ _≤_ (solve []) (solve (rho ∷ [])) outerRaw
      where
      open import Relation.Binary.PropositionalEquality using (subst₂)
  in
  trans
    (cong₂ _*_
      (clampedStep4AboveOne inner)
      (clampedStep4AboveOne outer))
    (ℚP.*-identityˡ 1ℚ)

round68CompactAnnularScalarCutoffConstructed : Bool
round68CompactAnnularScalarCutoffConstructed = true

round68CompactAnnularScalarCutoffConstructedIsTrue :
  round68CompactAnnularScalarCutoffConstructed ≡ true
round68CompactAnnularScalarCutoffConstructedIsTrue = refl
