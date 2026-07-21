module DASHI.Sheaf.GlobalAmbiguityBoundary where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Sheaf.FiniteTemporalClopenSheaf as Temporal
open import Verification.JacobianCounterexampleKernel as Jacobian
  using
    ( Point3
    ; F
    ; target
    ; pZero
    ; pPositive
    ; pZeroNotPositive
    ; pZeroImage
    ; pPositiveImage
    )

------------------------------------------------------------------------
-- Global ambiguity is a property of an observation/projection.  It is not a
-- failure of local compatibility and not a failure of sheaf gluing.

¬_ : Set → Set
¬ A = A → ⊥

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = ¬ (x ≡ y)

Injective : ∀ {A B : Set} → (A → B) → Set
Injective f = ∀ {x y} → f x ≡ f y → x ≡ y

record GlobalAmbiguity
    {Section Observation : Set}
    (observe : Section → Observation)
    : Set where
  constructor distinctSectionsSameObservation
  field
    firstSection secondSection : Section
    sectionsDistinct : firstSection ≢ secondSection
    observationsEqual : observe firstSection ≡ observe secondSection

open GlobalAmbiguity public

globalAmbiguityRefutesInjectivity :
  ∀ {Section Observation : Set} {observe : Section → Observation} →
  GlobalAmbiguity observe →
  ¬ Injective observe
globalAmbiguityRefutesInjectivity ambiguity injective =
  sectionsDistinct ambiguity
    (injective (observationsEqual ambiguity))

record GluingFailure
    {Left Right Global : Set}
    (Compatible : Left → Right → Set)
    (Glues : Global → Left → Right → Set)
    (left : Left)
    (right : Right)
    : Set₁ where
  field
    notCompatible : ¬ Compatible left right
    noGlobalGlue : (global : Global) → ¬ Glues global left right

------------------------------------------------------------------------
-- Finite temporal example.
--
-- Both local families are compatible and each has a unique global glue.  A
-- deliberately coarse observation that retains only the overlap value maps the
-- two distinct global sections to the same visible value.

firstGlobal secondGlobal : Temporal.GlobalSection
firstGlobal = Temporal.globalSection Temporal.absent Temporal.present Temporal.absent
secondGlobal = Temporal.globalSection Temporal.present Temporal.present Temporal.present

firstLeft : Temporal.LeftSection
firstLeft = Temporal.leftSection Temporal.absent Temporal.present

firstRight : Temporal.RightSection
firstRight = Temporal.rightSection Temporal.present Temporal.absent

secondLeft : Temporal.LeftSection
secondLeft = Temporal.leftSection Temporal.present Temporal.present

secondRight : Temporal.RightSection
secondRight = Temporal.rightSection Temporal.present Temporal.present

firstCompatible : Temporal.Compatible firstLeft firstRight
firstCompatible = Temporal.compatible Temporal.absent Temporal.present Temporal.absent

secondCompatible : Temporal.Compatible secondLeft secondRight
secondCompatible = Temporal.compatible Temporal.present Temporal.present Temporal.present

firstGlued : Temporal.Glues firstGlobal firstLeft firstRight
firstGlued = Temporal.glued Temporal.absent Temporal.present Temporal.absent

secondGlued : Temporal.Glues secondGlobal secondLeft secondRight
secondGlued = Temporal.glued Temporal.present Temporal.present Temporal.present

observeOverlap : Temporal.GlobalSection → Temporal.PNFValue
observeOverlap = Temporal.globalOverlap

firstGlobalNotSecond : firstGlobal ≢ secondGlobal
firstGlobalNotSecond ()

sameOverlapObservation :
  observeOverlap firstGlobal ≡ observeOverlap secondGlobal
sameOverlapObservation = refl

temporalGlobalAmbiguity : GlobalAmbiguity observeOverlap
temporalGlobalAmbiguity =
  distinctSectionsSameObservation
    firstGlobal
    secondGlobal
    firstGlobalNotSecond
    sameOverlapObservation

-- Unique gluing is preserved.  The ambiguity appears only after applying the
-- coarser observation map.
temporalObservationNotInjective : ¬ Injective observeOverlap
temporalObservationNotInjective =
  globalAmbiguityRefutesInjectivity temporalGlobalAmbiguity

------------------------------------------------------------------------
-- The polynomial map is another exact global-ambiguity instance.

jacobianGlobalAmbiguity : GlobalAmbiguity F
jacobianGlobalAmbiguity =
  distinctSectionsSameObservation
    pZero
    pPositive
    pZeroNotPositive
    (trans pZeroImage (sym pPositiveImage))

------------------------------------------------------------------------
-- Failure-mode taxonomy.

data FailureMode : Set where
  localOverlapConflict : FailureMode
  noCompatibleGlue : FailureMode
  multipleGluesForOneCompatibleFamily : FailureMode
  distinctGlobalsSameObservation : FailureMode

record GlobalAmbiguityReceipt : Set where
  constructor mkGlobalAmbiguityReceipt
  field
    mereViolStillMeansLocalConflict : Bool
    compatibleFamiliesStillGlue : Bool
    uniquenessForFixedLocalFamilyPreserved : Bool
    distinctGlobalSectionsCanShareObservation : Bool
    polynomialThreePointFibreInstantiated : Bool
    observationEqualityPromotedToStateEquality : Bool
    observationEqualityPromotedToStateEqualityIsFalse :
      observationEqualityPromotedToStateEquality ≡ false
    interpretation : String

globalAmbiguityReceipt : GlobalAmbiguityReceipt
globalAmbiguityReceipt =
  mkGlobalAmbiguityReceipt
    true true true true true
    false refl
    "MereViol is local incompatibility, while GlobalAmbiguity records loss of global identity under a noninjective observation; unique gluing for a fixed compatible family does not make every later projection injective"
