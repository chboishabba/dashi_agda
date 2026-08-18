module DASHI.Moonshine.AuxiliaryLevelHeckeEquivariantQuotientNoGoExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John Voight,
-- "Quaternion Algebras", Graduate Texts in Mathematics 288, Springer, 2021.
-- DOI: 10.1007/978-3-030-56694-4.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- David Blackwell,
-- "Equivalent Comparisons of Experiments", Annals of Mathematical Statistics
-- 24 (1953), 265--272. DOI: 10.1214/aoms/1177729032.
--
-- DASHI CONTRIBUTION
--
-- PR #585 originally isolated a sufficient structural explanation for marked
-- Hecke/deck blindness by assuming a literal product decomposition
--
--     MarkedState = GlobalHeckeFactor x DeckFactor
--
-- with good-prime Hecke acting only on the global coordinate.
--
-- That product is stronger than the observer theorem actually needs.
-- The exact minimal algebraic input is only an equivariant quotient
--
--          MarkedState  --T^M_ell-->  MarkedState
--              | q                       | q
--              v                         v
--          GlobalState  --T^G_ell-->  GlobalState
--
-- satisfying q(T^M_ell x)=T^G_ell(q x), together with a nontrivial q-fibre.
--
-- This module proves that under those hypotheses:
--
--   * every individual quotient-facing Hecke observer is constant on fibres;
--   * every finite family of such observers is non-separating on a nontrivial
--     fibre;
--   * the entire pointwise all-prime family is still non-separating;
--   * the coarse projection itself is non-separating;
--   * any source-native residual that distinguishes the fibre gives a strict
--     observer refinement (q,residual) > q.
--
-- The previous Cartesian-product theorem is recovered as a special case.
-- Therefore the remaining p=11 automorphic seam should seek the source-native
-- quotient/intertwining square first; a global x deck product decomposition is
-- useful when available but is no longer required for the all-Hecke no-go.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Moonshine.AuxiliaryLevelHeckeDeckFactorizationExact as Product

------------------------------------------------------------------------
-- Generic equivariant Hecke quotient.
------------------------------------------------------------------------

record HeckeEquivariantQuotient : Set₁ where
  field
    MarkedState : Set
    GlobalState : Set
    PrimeIndex : Set

    project : MarkedState → GlobalState
    markedHecke : PrimeIndex → MarkedState → MarkedState
    globalHecke : PrimeIndex → GlobalState → GlobalState

    intertwines : ∀ ell marked →
      project (markedHecke ell marked)
      ≡ globalHecke ell (project marked)

open HeckeEquivariantQuotient public

quotientHeckeObserver :
  (Q : HeckeEquivariantQuotient) →
  PrimeIndex Q → Observer.Observer (MarkedState Q) (GlobalState Q)
quotientHeckeObserver Q ell marked = project Q (markedHecke Q ell marked)

quotientHeckeObserverFactorsThroughProject :
  (Q : HeckeEquivariantQuotient) →
  (ell : PrimeIndex Q) →
  (marked : MarkedState Q) →
  quotientHeckeObserver Q ell marked
  ≡ globalHecke Q ell (project Q marked)
quotientHeckeObserverFactorsThroughProject Q ell marked = intertwines Q ell marked

------------------------------------------------------------------------
-- Any two points in one quotient fibre have identical Hecke readouts.
------------------------------------------------------------------------

sameFibreSamePrimeReadout :
  (Q : HeckeEquivariantQuotient) →
  (ell : PrimeIndex Q) →
  (left right : MarkedState Q) →
  project Q left ≡ project Q right →
  quotientHeckeObserver Q ell left
  ≡ quotientHeckeObserver Q ell right
sameFibreSamePrimeReadout Q ell left right sameProject =
  trans
    (intertwines Q ell left)
    (trans
      (cong (globalHecke Q ell) sameProject)
      (sym (intertwines Q ell right)))

record QuotientFibreCollision (Q : HeckeEquivariantQuotient) : Set where
  field
    collisionLeft collisionRight : MarkedState Q
    sameProject : project Q collisionLeft ≡ project Q collisionRight
    distinctMarked : collisionLeft ≡ collisionRight → ⊥

open QuotientFibreCollision public

projectCannotSeparateCollision :
  (Q : HeckeEquivariantQuotient) →
  QuotientFibreCollision Q →
  Observer.Separating (project Q) →
  ⊥
projectCannotSeparateCollision Q collision separating =
  distinctMarked collision
    (separating
      (collisionLeft collision)
      (collisionRight collision)
      (sameProject collision))

------------------------------------------------------------------------
-- Every finite prime family remains blind to a nontrivial quotient fibre.
------------------------------------------------------------------------

primeObserverFamily :
  (Q : HeckeEquivariantQuotient) →
  List (PrimeIndex Q) →
  Observer.ObserverFamily (MarkedState Q) (GlobalState Q)
primeObserverFamily Q [] = []
primeObserverFamily Q (ell ∷ ells) =
  quotientHeckeObserver Q ell ∷ primeObserverFamily Q ells

sameFibreAgreeOnPrimeList :
  (Q : HeckeEquivariantQuotient) →
  (ells : List (PrimeIndex Q)) →
  (left right : MarkedState Q) →
  project Q left ≡ project Q right →
  Observer.AgreeOn (primeObserverFamily Q ells) left right
sameFibreAgreeOnPrimeList Q [] left right same = tt
sameFibreAgreeOnPrimeList Q (ell ∷ ells) left right same =
  sameFibreSamePrimeReadout Q ell left right same
  , sameFibreAgreeOnPrimeList Q ells left right same

finitePrimeFamilyCannotSeparateCollision :
  (Q : HeckeEquivariantQuotient) →
  QuotientFibreCollision Q →
  (ells : List (PrimeIndex Q)) →
  Observer.SeparatingFamily (primeObserverFamily Q ells) →
  ⊥
finitePrimeFamilyCannotSeparateCollision Q collision ells separating =
  distinctMarked collision
    (separating
      (collisionLeft collision)
      (collisionRight collision)
      (sameFibreAgreeOnPrimeList
        Q ells
        (collisionLeft collision)
        (collisionRight collision)
        (sameProject collision)))

------------------------------------------------------------------------
-- Pointwise all-prime blindness.  No function extensionality is required.
------------------------------------------------------------------------

AllPrimeAgreement :
  (Q : HeckeEquivariantQuotient) →
  MarkedState Q → MarkedState Q → Set
AllPrimeAgreement Q left right =
  (ell : PrimeIndex Q) →
  quotientHeckeObserver Q ell left ≡ quotientHeckeObserver Q ell right

AllPrimeSeparating : (Q : HeckeEquivariantQuotient) → Set
AllPrimeSeparating Q =
  (left right : MarkedState Q) →
  AllPrimeAgreement Q left right →
  left ≡ right

sameFibreAgreeAtAllPrimes :
  (Q : HeckeEquivariantQuotient) →
  (left right : MarkedState Q) →
  project Q left ≡ project Q right →
  AllPrimeAgreement Q left right
sameFibreAgreeAtAllPrimes Q left right same ell =
  sameFibreSamePrimeReadout Q ell left right same

allPrimeFamilyCannotSeparateCollision :
  (Q : HeckeEquivariantQuotient) →
  QuotientFibreCollision Q →
  AllPrimeSeparating Q →
  ⊥
allPrimeFamilyCannotSeparateCollision Q collision separating =
  distinctMarked collision
    (separating
      (collisionLeft collision)
      (collisionRight collision)
      (sameFibreAgreeAtAllPrimes
        Q
        (collisionLeft collision)
        (collisionRight collision)
        (sameProject collision)))

------------------------------------------------------------------------
-- A source-native residual gives a strict refinement of the Hecke quotient.
------------------------------------------------------------------------

record ResidualSeparatesCollision
    (Q : HeckeEquivariantQuotient)
    (collision : QuotientFibreCollision Q) : Set₁ where
  field
    Residual : Set
    residual : MarkedState Q → Residual
    residualSeparates :
      residual (collisionLeft collision)
      ≡ residual (collisionRight collision) → ⊥

open ResidualSeparatesCollision public

residualStrictlyRefinesProject :
  (Q : HeckeEquivariantQuotient) →
  (collision : QuotientFibreCollision Q) →
  (witness : ResidualSeparatesCollision Q collision) →
  Observer.StrictRefinement
    (project Q)
    (Observer.pairObserver (project Q) (residual witness))
residualStrictlyRefinesProject Q collision witness =
  Observer.strictPairRefinement
    (project Q)
    (residual witness)
    (collisionLeft collision)
    (collisionRight collision)
    (sameProject collision)
    (residualSeparates witness)

------------------------------------------------------------------------
-- The older product-factor mechanism is a special case of the weaker
-- equivariant-quotient theorem.
------------------------------------------------------------------------

productAsEquivariantQuotient :
  Product.AuxiliaryLevelHeckeFactorization → HeckeEquivariantQuotient
productAsEquivariantQuotient F = record
  { MarkedState = Product.MarkedState F
  ; GlobalState = Product.GlobalState F
  ; PrimeIndex = Product.PrimeIndex F
  ; project = fst
  ; markedHecke = Product.markedHecke F
  ; globalHecke = Product.globalHecke F
  ; intertwines = λ ell marked → refl
  }

productFibreCollision :
  (F : Product.AuxiliaryLevelHeckeFactorization) →
  (global : Product.GlobalState F) →
  (deck0 deck1 : Product.DeckState F) →
  (deck0 ≡ deck1 → ⊥) →
  QuotientFibreCollision (productAsEquivariantQuotient F)
productFibreCollision F global deck0 deck1 deckDistinct = record
  { collisionLeft = global , deck0
  ; collisionRight = global , deck1
  ; sameProject = refl
  ; distinctMarked = λ markedSame → deckDistinct (cong snd markedSame)
  }

record EquivariantQuotientNoGoBoundary : Set where
  field
    productFactorizationRequiredForBlindness : Bool
    productFactorizationRequiredForBlindnessIsFalse :
      productFactorizationRequiredForBlindness ≡ false

    equivariantQuotientSufficientForAllPrimeBlindness : Bool
    equivariantQuotientSufficientForAllPrimeBlindnessIsTrue :
      equivariantQuotientSufficientForAllPrimeBlindness ≡ true

    sourceNativeResidualStillRequiredForRepair : Bool
    sourceNativeResidualStillRequiredForRepairIsTrue :
      sourceNativeResidualStillRequiredForRepair ≡ true

canonicalEquivariantQuotientNoGoBoundary : EquivariantQuotientNoGoBoundary
canonicalEquivariantQuotientNoGoBoundary = record
  { productFactorizationRequiredForBlindness = false
  ; productFactorizationRequiredForBlindnessIsFalse = refl
  ; equivariantQuotientSufficientForAllPrimeBlindness = true
  ; equivariantQuotientSufficientForAllPrimeBlindnessIsTrue = refl
  ; sourceNativeResidualStillRequiredForRepair = true
  ; sourceNativeResidualStillRequiredForRepairIsTrue = refl
  }
