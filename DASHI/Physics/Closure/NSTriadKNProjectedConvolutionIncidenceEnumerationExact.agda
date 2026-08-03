module DASHI.Physics.Closure.NSTriadKNProjectedConvolutionIncidenceEnumerationExact where

------------------------------------------------------------------------
-- PURPOSE
-- Give the projected-convolution lane a finite exact-enumeration interface
-- that distinguishes triad records from pair-incidence slots.  Every triad
-- contributes exactly three tagged incidences.  Two distinct incidences may
-- share the same source/target image; multiplicity is preserved by the slot
-- tag and must agree with the physical convolution fibre.
--
-- The interface is repository-original and has no external DOI.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; _≢_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_; length)

------------------------------------------------------------------------
-- Membership and duplicate freedom, kept local to avoid depending on a
-- particular standard-library Unique API.
------------------------------------------------------------------------

infix 4 _∈_
data _∈_ {ℓ : Level} {A : Set ℓ} (value : A) : List A → Set ℓ where
  here : ∀ {values} → value ∈ (value ∷ values)
  there : ∀ {head values} → value ∈ values → value ∈ (head ∷ values)

data NoDuplicates {ℓ : Level} {A : Set ℓ} : List A → Set ℓ where
  empty : NoDuplicates []
  prepend :
    ∀ {head values} →
    (head ∈ values → ⊥) →
    NoDuplicates values →
    NoDuplicates (head ∷ values)

record ExactFiniteEnumeration
    {ℓ : Level}
    {A : Set ℓ}
    (Admissible : A → Set ℓ) : Set (lsuc ℓ) where
  constructor exact-enumeration
  field
    values : List A
    sound : (value : A) → value ∈ values → Admissible value
    complete : (value : A) → Admissible value → value ∈ values
    noDuplicates : NoDuplicates values

open ExactFiniteEnumeration public

------------------------------------------------------------------------
-- Triads and their three incidence slots.
------------------------------------------------------------------------

data PairIncidenceSlot : Set where
  leftRightSlot
  leftOutputSlot
  rightOutputSlot : PairIncidenceSlot

record ProjectedConvolutionTriad {ℓ : Level} (Mode : Set ℓ) : Set ℓ where
  constructor triad
  field
    leftMode : Mode
    rightMode : Mode
    outputMode : Mode

open ProjectedConvolutionTriad public

record TaggedPairIncidence
    {ℓ : Level}
    {Mode : Set ℓ}
    (Triad : Set ℓ) : Set ℓ where
  constructor incidence
  field
    parentTriad : Triad
    slot : PairIncidenceSlot

open TaggedPairIncidence public

expandTriad :
  ∀ {ℓ} {Mode : Set ℓ} →
  (Triad : Set ℓ) →
  Triad → List (TaggedPairIncidence Triad)
expandTriad Triad value =
  incidence value leftRightSlot
  ∷ incidence value leftOutputSlot
  ∷ incidence value rightOutputSlot
  ∷ []

three : Nat
three = suc (suc (suc zero))

triadContributesExactlyThreeIncidences :
  ∀ {ℓ} {Mode : Set ℓ}
    (Triad : Set ℓ)
    (value : Triad) →
  length (expandTriad Triad value) ≡ three
triadContributesExactlyThreeIncidences Triad value = refl

record ExactProjectedConvolutionTriadEnumeration
    {ℓ : Level}
    (Mode : Set ℓ) : Set (lsuc ℓ) where
  field
    AdmissibleTriad : ProjectedConvolutionTriad Mode → Set ℓ
    enumeration : ExactFiniteEnumeration AdmissibleTriad

    highProjectorCutoffConventionMatches : Set ℓ
    convolutionResonanceConventionMatches : Set ℓ
    zeroModeConventionMatches : Set ℓ

open ExactProjectedConvolutionTriadEnumeration public

record ExactProjectedPairIncidenceEnumeration
    {ℓ : Level}
    (Mode : Set ℓ) : Set (lsuc ℓ) where
  field
    triads : ExactProjectedConvolutionTriadEnumeration Mode

    Incidence : Set ℓ
    incidenceValues : List Incidence

    sourceMode : Incidence → Mode
    targetMode : Incidence → Mode
    parent : Incidence → ProjectedConvolutionTriad Mode
    slotOf : Incidence → PairIncidenceSlot

    incidenceSound : Set ℓ
    incidenceComplete : Set ℓ
    incidenceNoDuplicates : NoDuplicates incidenceValues

    eachTriadContributesThreeTaggedSlots :
      (value : ProjectedConvolutionTriad Mode) →
      length
        (expandTriad
          (ProjectedConvolutionTriad Mode)
          value)
        ≡ three

open ExactProjectedPairIncidenceEnumeration public

record PhysicalFibreMultiplicityAgreement
    {ℓM ℓI : Level}
    (Mode : Set ℓM)
    (Incidence : Set ℓI) : Set (lsuc (ℓM)) where
  field
    physicalConvolutionFibre : Mode → Mode → List Incidence
    enumeratedPairIncidenceFibre : Mode → Mode → List Incidence

    fibresAgreeWithMultiplicity :
      (source target : Mode) →
      enumeratedPairIncidenceFibre source target
        ≡ physicalConvolutionFibre source target

open PhysicalFibreMultiplicityAgreement public

fibreLengthsAgree :
  ∀ {ℓM ℓI}
    {Mode : Set ℓM}
    {Incidence : Set ℓI}
    (agreement : PhysicalFibreMultiplicityAgreement Mode Incidence) →
    (source target : Mode) →
  length (enumeratedPairIncidenceFibre agreement source target)
    ≡ length (physicalConvolutionFibre agreement source target)
fibreLengthsAgree agreement source target =
  congLength (fibresAgreeWithMultiplicity agreement source target)
  where
    congLength : ∀ {A : Set ℓI} {left right : List A} →
      left ≡ right → length left ≡ length right
    congLength refl = refl

taggedThreeSlotExpansionConstructed : Bool
taggedThreeSlotExpansionConstructed = true

multiplicityPreservingEnumerationInterfaceConstructed : Bool
multiplicityPreservingEnumerationInterfaceConstructed = true

physicalProjectedConvolutionTriadEnumerationInhabited : Bool
physicalProjectedConvolutionTriadEnumerationInhabited = false

physicalProjectedPairIncidenceEnumerationInhabited : Bool
physicalProjectedPairIncidenceEnumerationInhabited = false

taggedThreeSlotExpansionConstructedIsTrue :
  taggedThreeSlotExpansionConstructed ≡ true
taggedThreeSlotExpansionConstructedIsTrue = refl

multiplicityPreservingEnumerationInterfaceConstructedIsTrue :
  multiplicityPreservingEnumerationInterfaceConstructed ≡ true
multiplicityPreservingEnumerationInterfaceConstructedIsTrue = refl

physicalProjectedConvolutionTriadEnumerationInhabitedIsFalse :
  physicalProjectedConvolutionTriadEnumerationInhabited ≡ false
physicalProjectedConvolutionTriadEnumerationInhabitedIsFalse = refl

physicalProjectedPairIncidenceEnumerationInhabitedIsFalse :
  physicalProjectedPairIncidenceEnumerationInhabited ≡ false
physicalProjectedPairIncidenceEnumerationInhabitedIsFalse = refl
