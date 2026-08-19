module DASHI.Moonshine.DuncanSwisherThreeObserverExponentWeldExact where

------------------------------------------------------------------------
-- THREE SOURCE-NATIVE OBSERVERS OF ONE MONSTER EXPONENT CONSUMER
--
-- PRIMARY SOURCE
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents", 2026.
-- arXiv:2602.09135. DOI: 10.48550/arXiv.2602.09135.
--
-- Existing repo owners already expose two distinct observers of
--
--   2 v_p(|M|):
--
--   geometric: supersingular Frobenius stratum + m_p,
--   modular:   three Hauptmodul valuation contributions.
--
-- Remark 1.4 supplies a third source-native presentation of the same scale:
--
--   d_Faber := v_p(j|V_p-Phi_p(j)) = m_p.
--
-- DASHI CONTRIBUTION
--
-- Add the Faber observer WITHOUT identifying its Laurent-series carrier with
-- either previous carrier.  Its correct sufficient statistic is
--
--   Frobenius regime + Faber depth,
--
-- not Faber depth alone.  The p=13 / p=37 control is exact:
-- both have m_p=d_Faber=2, while their Monster valuations are 3 and 0.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat using (_≤_; _*_)
open import Data.Nat.Primality using (Prime)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.DuncanSwisherMonsterExponentFormulaExact as DS
import DASHI.Moonshine.DuncanSwisherModularValuationDepthMechanismExact as Modular
import DASHI.Moonshine.DuncanSwisherExponentObserverFactorizationExact as Existing
import DASHI.Moonshine.DuncanSwisherFaberVpDepthExact as Faber

------------------------------------------------------------------------
-- One theorem state carrying all three source-native mechanisms.
------------------------------------------------------------------------

record ThreeObserverExponentState
    (p : Nat) (prime : Prime p) (ge5 : 5 ≤ p) : Set₁ where
  constructor three-observer-exponent-state
  field
    exponentAuthority : DS.DuncanSwisherExponentAuthority p prime ge5
    modularAuthority :
      Modular.DuncanSwisherModularValuationAuthority
        p prime ge5 exponentAuthority
    faberAuthority : Faber.DuncanSwisherFaberVpAuthority p
    faberDepthEqualsMinimum :
      Faber.discrepancyDepth faberAuthority
      ≡ DS.minimumAutomorphismOrder exponentAuthority

open ThreeObserverExponentState public

postulate
  publishedThreeObserverExponentState :
    (p : Nat) → (prime : Prime p) → (ge5 : 5 ≤ p) →
    ThreeObserverExponentState p prime ge5

------------------------------------------------------------------------
-- Reuse the existing exact three-way Frobenius regime type.
------------------------------------------------------------------------

record FaberDepthCode : Set where
  constructor faber-depth-code
  field
    stratum : Existing.ExponentStratum
    faberDepth : Nat

open FaberDepthCode public

stratumOfExponentAuthority :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  DS.DuncanSwisherExponentAuthority p prime ge5 →
  Existing.ExponentStratum
stratumOfExponentAuthority E =
  Existing.stratum (Existing.geometricDepthCodeOf E)

faberObserver :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ThreeObserverExponentState p prime ge5 →
  FaberDepthCode
faberObserver state = faber-depth-code
  (stratumOfExponentAuthority (exponentAuthority state))
  (Faber.discrepancyDepth (faberAuthority state))

depthFromFaber : FaberDepthCode → Nat
depthFromFaber (faber-depth-code Existing.singletonRationalStratum d) = 3 * d
depthFromFaber (faber-depth-code Existing.multipleRationalStratum d) = d
depthFromFaber (faber-depth-code Existing.quadraticStratum d) = 0

doubledMonsterValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ThreeObserverExponentState p prime ge5 → Nat
doubledMonsterValuation state =
  2 * DS.monsterValuation (exponentAuthority state)

------------------------------------------------------------------------
-- Faber regime+depth computes the SAME doubled Monster valuation.
------------------------------------------------------------------------

faberComputesDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ThreeObserverExponentState p prime ge5) →
  depthFromFaber (faberObserver state)
  ≡ doubledMonsterValuation state
faberComputesDoubledValuation state
  with DS.theorem12 (exponentAuthority state)
... | DS.singletonRational fixedOne pairedZero doubled =
  trans
    (cong (λ n → 3 * n) (faberDepthEqualsMinimum state))
    (sym doubled)
... | DS.multipleRational fixedMany pairedZero doubled =
  trans (faberDepthEqualsMinimum state) (sym doubled)
... | DS.quadraticPresent pairedPositive valuationZero minTwo
  rewrite valuationZero = refl

faberObserverSufficientForDoubledValuation :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  Observer.Refines
    (doubledMonsterValuation {p = p} {prime = prime} {ge5 = ge5})
    faberObserver
faberObserverSufficientForDoubledValuation left right sameFaber =
  trans
    (sym (faberComputesDoubledValuation left))
    (trans
      (cong depthFromFaber sameFaber)
      (faberComputesDoubledValuation right))

------------------------------------------------------------------------
-- Existing geometric and modular observers meet the new Faber observer only at
-- the declared consumer; their carriers remain distinct.
------------------------------------------------------------------------

asExistingState :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  ThreeObserverExponentState p prime ge5 →
  Existing.ExponentMechanismState p prime ge5
asExistingState state = Existing.exponentMechanismState
  (exponentAuthority state)
  (modularAuthority state)

geometryAndFaberOutputsAgree :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ThreeObserverExponentState p prime ge5) →
  Existing.depthFromGeometry
    (Existing.geometricObserver (asExistingState state))
  ≡ depthFromFaber (faberObserver state)
geometryAndFaberOutputsAgree state =
  trans
    (Existing.geometryComputesDoubledValuation (asExistingState state))
    (sym (faberComputesDoubledValuation state))

modularAndFaberOutputsAgree :
  ∀ {p : Nat} {prime : Prime p} {ge5 : 5 ≤ p} →
  (state : ThreeObserverExponentState p prime ge5) →
  Existing.depthFromModular
    (Existing.modularObserver (asExistingState state))
  ≡ depthFromFaber (faberObserver state)
modularAndFaberOutputsAgree state =
  trans
    (Existing.modularComputesDoubledValuation (asExistingState state))
    (sym (faberComputesDoubledValuation state))

------------------------------------------------------------------------
-- Faber depth ALONE is not sufficient: p=13 and p=37 both have m_p=2 but
-- different Frobenius regimes and different Monster exponent outputs.
------------------------------------------------------------------------

data FaberDepthControl : Set where
  control13 control37 : FaberDepthControl

faberDepthOnlyControl : FaberDepthControl → Nat
faberDepthOnlyControl control13 = 2
faberDepthOnlyControl control37 = 2

doubledMonsterControl : FaberDepthControl → Nat
doubledMonsterControl control13 = 6
doubledMonsterControl control37 = 0

control13DepthMatchesSourceMp :
  faberDepthOnlyControl control13 ≡ 2
control13DepthMatchesSourceMp = refl

control37DepthMatchesSourceMp :
  faberDepthOnlyControl control37 ≡ 2
control37DepthMatchesSourceMp = refl

control13DoubledExponentMatchesTheorem12 :
  doubledMonsterControl control13 ≡ 3 * 2
control13DoubledExponentMatchesTheorem12 = refl

control37DoubledExponentMatchesTheorem12 :
  doubledMonsterControl control37 ≡ 0
control37DoubledExponentMatchesTheorem12 = refl

sixNotZero : 6 ≡ 0 → ⊥
sixNotZero ()

faberDepthAloneCannotDecodeExponent :
  (decode : Nat → Nat) →
  decode (faberDepthOnlyControl control13) ≡ doubledMonsterControl control13 →
  decode (faberDepthOnlyControl control37) ≡ doubledMonsterControl control37 →
  ⊥
faberDepthAloneCannotDecodeExponent decode at13 at37 =
  sixNotZero
    (trans
      (sym at13)
      (trans
        (cong decode refl)
        at37))

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DuncanSwisherThreeObserverExponentBoundary : Set where
  field
    geometricObserverRetained : Bool
    modularObserverRetained : Bool
    faberObserverAdded : Bool
    allThreeComputeSameDoubledExponent : Bool
    observerCarriersIdentified : Bool
    faberDepthAloneSufficient : Bool
    frobeniusRegimePlusFaberDepthSufficient : Bool
    p13p37SameDepthDifferentExponentFalsifier : Bool
    lowPrimeTwoThreePromoted : Bool

canonicalDuncanSwisherThreeObserverExponentBoundary :
  DuncanSwisherThreeObserverExponentBoundary
canonicalDuncanSwisherThreeObserverExponentBoundary = record
  { geometricObserverRetained = true
  ; modularObserverRetained = true
  ; faberObserverAdded = true
  ; allThreeComputeSameDoubledExponent = true
  ; observerCarriersIdentified = false
  ; faberDepthAloneSufficient = false
  ; frobeniusRegimePlusFaberDepthSufficient = true
  ; p13p37SameDepthDifferentExponentFalsifier = true
  ; lowPrimeTwoThreePromoted = false
  }
