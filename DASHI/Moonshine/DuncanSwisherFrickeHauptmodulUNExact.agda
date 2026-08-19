module DASHI.Moonshine.DuncanSwisherFrickeHauptmodulUNExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Section 2 defines U_N and proves its level-lowering properties.  On the
-- prime Fricke genus-zero branch, Lemmas 2.7/2.9 give the same-object identity
--
--   p (J_p^+ | U_p) + (J_p^+ | W_p) = J_1.
--
-- Since the normalized Fricke Hauptmodul is W_p-invariant,
--
--   J_1 - J_p^+ = p (J_p^+ | U_p).
--
-- DASHI CONTRIBUTION
--
-- Pin that published modular-function identity at one explicit source boundary
-- and lower it to the repository's already-constructed SIGNED Laurent
-- coefficient carrier.  Using
--
--   c_n(f | U_p) = c_{pn}(f),
--
-- derive for every signed Laurent index n
--
--   c_n(J_1) - c_n(J_p^+) = p * c_{pn}(J_p^+).
--
-- This is the exact interface needed by the later p-adic valuation/Deligne
-- argument.  It does not yet construct eta-quotient Hauptmoduls or Deligne's
-- supersingular partial-fraction expansion.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ; +_)
import Data.Integer as Int
import Data.Integer.Tactic.RingSolver as ℤRing
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Moonshine.DuncanSwisherUNModularLevelAuthorityExact as UN
import DASHI.Moonshine.FormalLaurentQSeriesUNExact as Laurent

------------------------------------------------------------------------
-- Published p-specific Hauptmodul identity.
------------------------------------------------------------------------

record PrimeFrickeHauptmodulUNAuthority (p : Nat) : Set where
  field
    levelOneHauptmodul : UN.ModularFunction
    primeFrickeHauptmodul : UN.ModularFunction

    -- The source's Fricke invariance is retained explicitly, rather than hidden
    -- inside the already-simplified coefficient equation.
    frickeAction : UN.ModularFunction → UN.ModularFunction
    primeHauptmodulFrickeInvariant :
      frickeAction primeFrickeHauptmodul ≡ primeFrickeHauptmodul

    -- Lemma 2.9 / level-lowering identity on the actual modular functions.
    levelLoweringIdentityAt :
      (n : ℤ) →
      UN.qExpansion levelOneHauptmodul n
      ≡
      Int._+_
        (Int._*_ (+ p) (UN.qExpansion (UN.analyticUN p primeFrickeHauptmodul) n))
        (UN.qExpansion (frickeAction primeFrickeHauptmodul) n)

open PrimeFrickeHauptmodulUNAuthority public

postulate
  publishedPrimeFrickeHauptmodulUNAuthority :
    (p : Nat) → PrimeFrickeHauptmodulUNAuthority p

------------------------------------------------------------------------
-- First simplify the Fricke term on coefficients using SAME-OBJECT equality.
------------------------------------------------------------------------

frickeInvariantCoefficient :
  {p : Nat} →
  (A : PrimeFrickeHauptmodulUNAuthority p) →
  (n : ℤ) →
  UN.qExpansion (frickeAction A (primeFrickeHauptmodul A)) n
  ≡ UN.qExpansion (primeFrickeHauptmodul A) n
frickeInvariantCoefficient A n =
  cong (λ f → UN.qExpansion f n) (primeHauptmodulFrickeInvariant A)

------------------------------------------------------------------------
-- Exact coefficient form of J_1 - J_p^+ = p U_p J_p^+.
------------------------------------------------------------------------

hauptmodulDifferenceIsScaledUNAt :
  {p : Nat} →
  (A : PrimeFrickeHauptmodulUNAuthority p) →
  (n : ℤ) →
  Int._-_ (UN.qExpansion (levelOneHauptmodul A) n)
          (UN.qExpansion (primeFrickeHauptmodul A) n)
  ≡ Int._*_ (+ p)
      (UN.qExpansion (UN.analyticUN p (primeFrickeHauptmodul A)) n)
hauptmodulDifferenceIsScaledUNAt {p} A n =
  let
    source = levelLoweringIdentityAt A n
    fricke = frickeInvariantCoefficient A n
    a = UN.qExpansion (levelOneHauptmodul A) n
    b = UN.qExpansion (UN.analyticUN p (primeFrickeHauptmodul A)) n
    c = UN.qExpansion (frickeAction A (primeFrickeHauptmodul A)) n
    d = UN.qExpansion (primeFrickeHauptmodul A) n
  in
  subst
    (λ c' → Int._-_ a d ≡ Int._*_ (+ p) b)
    fricke
    (subst
      (λ a' → Int._-_ a' d ≡ Int._*_ (+ p) b)
      source
      (ℤRing.solve ((+ p) ∷ b ∷ d ∷ [])))

------------------------------------------------------------------------
-- Now consume the already-pinned analytic U_p coefficient selector.
------------------------------------------------------------------------

hauptmodulDifferenceSelectsPMultipleAt :
  {p : Nat} →
  (A : PrimeFrickeHauptmodulUNAuthority p) →
  (n : ℤ) →
  Int._-_ (UN.qExpansion (levelOneHauptmodul A) n)
          (UN.qExpansion (primeFrickeHauptmodul A) n)
  ≡ Int._*_ (+ p)
      (UN.qExpansion (primeFrickeHauptmodul A) (Int._*_ (+ p) n))
hauptmodulDifferenceSelectsPMultipleAt {p} A n =
  trans
    (hauptmodulDifferenceIsScaledUNAt A n)
    (cong (Int._*_ (+ p))
      (UN.analyticUNCoefficientIsSelectedSource p (primeFrickeHauptmodul A) n))

------------------------------------------------------------------------
-- Formal Laurent readout.  This states exactly that the modular-function
-- theorem and the existing signed coefficient-selection operator agree.
------------------------------------------------------------------------

primeFrickeSeries :
  {p : Nat} → PrimeFrickeHauptmodulUNAuthority p → Laurent.FormalLaurentQSeries
primeFrickeSeries A = UN.qExpansion (primeFrickeHauptmodul A)

levelOneSeries :
  {p : Nat} → PrimeFrickeHauptmodulUNAuthority p → Laurent.FormalLaurentQSeries
levelOneSeries A = UN.qExpansion (levelOneHauptmodul A)

selectedPrimeFrickeCoefficient :
  {p : Nat} →
  (A : PrimeFrickeHauptmodulUNAuthority p) →
  (n : ℤ) →
  Laurent.UN p (primeFrickeSeries A) n
  ≡ UN.qExpansion (primeFrickeHauptmodul A) (Int._*_ (+ p) n)
selectedPrimeFrickeCoefficient A n = refl

record DuncanSwisherFrickeHauptmodulUNBoundary : Set where
  field
    publishedFrickeHauptmodulIdentityImported : Bool
    frickeInvarianceKeptSameObject : Bool
    signedLaurentCarrierReused : Bool
    coefficientDifferenceLawDerived : Bool
    pMultipleSelectionLawDerived : Bool
    etaQuotientHauptmodulConstructedHere : Bool
    DeligneSupersingularExpansionConstructedHere : Bool

canonicalDuncanSwisherFrickeHauptmodulUNBoundary :
  DuncanSwisherFrickeHauptmodulUNBoundary
canonicalDuncanSwisherFrickeHauptmodulUNBoundary = record
  { publishedFrickeHauptmodulIdentityImported = true
  ; frickeInvarianceKeptSameObject = true
  ; signedLaurentCarrierReused = true
  ; coefficientDifferenceLawDerived = true
  ; pMultipleSelectionLawDerived = true
  ; etaQuotientHauptmodulConstructedHere = false
  ; DeligneSupersingularExpansionConstructedHere = false
  }
