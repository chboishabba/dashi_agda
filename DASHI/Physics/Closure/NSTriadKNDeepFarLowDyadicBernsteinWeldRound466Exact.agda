module DASHI.Physics.Closure.NSTriadKNDeepFarLowDyadicBernsteinWeldRound466Exact where

------------------------------------------------------------------------
-- ROUND466 / EXISTING DYADIC SUPPORT COUNT -> R465 -> R234
--
-- R465 reuses the repository's original finite rational Bernstein theorem.
-- Its shell-routing input is paid here from the already-proved Luo dyadic
-- support count
--
--   count(selected_q) <= 8^q count(base).
--
-- The coefficient list is literally `map coefficient selected_q`; therefore
-- its Bernstein support cardinality is exactly the same count mass.  If the
-- physical high derivative coefficient dominates the existing dyadic capacity,
-- the complete R234 scalar deep-FL payment follows with no new inequality.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (map)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Bernstein
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicSupportCountExact as Support
import DASHI.Physics.Closure.NSTriadKNRationalFiniteGeometricEnvelope as Geo
import DASHI.Physics.Closure.NSTriadKNRationalInfinityShellBernsteinRound465Exact as R465
import DASHI.Physics.Closure.NSTriadKNDeepFarLowCriticalShoulderRound234Exact as R234

supportCardinalityMapMeaning :
  ∀ {A : Set} (coefficient : A → ℚ) (items : List A) →
  Bernstein.supportCardinality (map coefficient items)
  ≡ Support.countMass items
supportCardinalityMapMeaning coefficient [] = refl
supportCardinalityMapMeaning coefficient (item ∷ items) =
  cong (1ℚ +_) (supportCardinalityMapMeaning coefficient items)

record PhysicalDeepFarLowDyadicData (Slot : Set) : Set₁ where
  constructor physical-deep-far-low-dyadic-data
  field
    shellPredicate : Slot → Bool
    baseCube : List Slot
    shell : Nat
    coefficient : Slot → ℚ

    highEnergy highDerivativeCoefficient productMass : ℚ
    highEnergyNN : 0ℚ ≤ highEnergy
    highDerivativeCoefficientNN : 0ℚ ≤ highDerivativeCoefficient

    dyadicCapacityPaidByDerivative :
      Geo.pow Support.eight shell * Support.countMass baseCube
      ≤ highDerivativeCoefficient

    productMassBelowFiniteBernsteinInput :
      productMass
      ≤ Rational.square
          (Bernstein.coefficientSum
            (map coefficient
              (Support.dyadicSupport shellPredicate baseCube shell)))
          * highEnergy

open PhysicalDeepFarLowDyadicData public

retainedSlots :
  ∀ {Slot : Set} → PhysicalDeepFarLowDyadicData Slot → List Slot
retainedSlots D = Support.dyadicSupport
  (shellPredicate D) (baseCube D) (shell D)

retainedCoefficients :
  ∀ {Slot : Set} → PhysicalDeepFarLowDyadicData Slot → List ℚ
retainedCoefficients D = map (coefficient D) (retainedSlots D)

retainedCardinalityPaidByDerivative :
  ∀ {Slot : Set} (D : PhysicalDeepFarLowDyadicData Slot) →
  Bernstein.supportCardinality (retainedCoefficients D)
  ≤ highDerivativeCoefficient D
retainedCardinalityPaidByDerivative D =
  let
    selectedCount = Support.dyadicSupportCountBound
      (shellPredicate D) (baseCube D) (shell D)
    toDerivative = ℚP.≤-trans selectedCount (dyadicCapacityPaidByDerivative D)
  in
  subst
    (λ lower → lower ≤ highDerivativeCoefficient D)
    (sym (supportCardinalityMapMeaning (coefficient D) (retainedSlots D)))
    toDerivative

toR465FiniteBernsteinData :
  ∀ {Slot : Set} →
  PhysicalDeepFarLowDyadicData Slot → R465.DeepFarLowFiniteBernsteinData
toR465FiniteBernsteinData D = record
  { R465.coefficients = retainedCoefficients D
  ; R465.highEnergy = highEnergy D
  ; R465.highDerivativeCoefficient = highDerivativeCoefficient D
  ; R465.productMass = productMass D
  ; R465.highEnergyNN = highEnergyNN D
  ; R465.highDerivativeCoefficientNN = highDerivativeCoefficientNN D
  ; R465.supportCardinalityPaidByDerivative =
      retainedCardinalityPaidByDerivative D
  ; R465.productMassBelowBernsteinInput =
      productMassBelowFiniteBernsteinInput D
  }

toR234DeepFarLowPayment :
  ∀ {Slot : Set} →
  PhysicalDeepFarLowDyadicData Slot → R234.DeepFarLowScalarPayment
toR234DeepFarLowPayment D =
  R465.toR234DeepFarLowScalarPayment (toR465FiniteBernsteinData D)

deepFarLowDyadicMassPaidByEnergyDissipation :
  ∀ {Slot : Set} (D : PhysicalDeepFarLowDyadicData Slot) →
  productMass D
  ≤ Bernstein.coefficientNormSquared (retainedCoefficients D)
      * R234.highDissipation (toR234DeepFarLowPayment D)
deepFarLowDyadicMassPaidByEnergyDissipation D =
  R465.deepFarLowFiniteBernsteinPaidByEnergyDissipation
    (toR465FiniteBernsteinData D)

round466ExistingDyadicSupportCountReused : Bool
round466ExistingDyadicSupportCountReused = true

round466ExistingFiniteBernsteinReused : Bool
round466ExistingFiniteBernsteinReused = true

round466DeepFarLowDyadicCompilerClosed : Bool
round466DeepFarLowDyadicCompilerClosed = true

round466NewBernsteinInequalityIntroduced : Bool
round466NewBernsteinInequalityIntroduced = false

round466LiteralPhysicalShellCoefficientExtractionStillRequired : Bool
round466LiteralPhysicalShellCoefficientExtractionStillRequired = true

round466ContainsPostulate : Bool
round466ContainsPostulate = false

round466PackageAClosed : Bool
round466PackageAClosed = false

round466ClayPromotion : Bool
round466ClayPromotion = false

round466NewBernsteinInequalityIntroducedIsFalse :
  round466NewBernsteinInequalityIntroduced ≡ false
round466NewBernsteinInequalityIntroducedIsFalse = refl

round466ContainsPostulateIsFalse : round466ContainsPostulate ≡ false
round466ContainsPostulateIsFalse = refl
