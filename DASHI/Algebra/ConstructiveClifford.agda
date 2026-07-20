module DASHI.Algebra.ConstructiveClifford where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Geometry.FlatLorentzianModel using
  (Axis4; timeAxis; xAxis; yAxis; zAxis)
import DASHI.Unified.GRQuantumProofTerms as ProofTerms

------------------------------------------------------------------------
-- Concrete syntax and relations for Cl(3,1).


data ScalarSign : Set where
  negative : ScalarSign
  zero : ScalarSign
  positive : ScalarSign

metricSquare : Axis4 → ScalarSign
metricSquare timeAxis = negative
metricSquare xAxis = positive
metricSquare yAxis = positive
metricSquare zAxis = positive


data CliffordWord : Set where
  scalarWord : ScalarSign → CliffordWord
  generator : Axis4 → CliffordWord
  _∙_ : CliffordWord → CliffordWord → CliffordWord

infixl 7 _∙_

------------------------------------------------------------------------
-- Generated Clifford congruence.


data DistinctAxis : Axis4 → Axis4 → Set where
  time-x : DistinctAxis timeAxis xAxis
  time-y : DistinctAxis timeAxis yAxis
  time-z : DistinctAxis timeAxis zAxis
  x-time : DistinctAxis xAxis timeAxis
  x-y : DistinctAxis xAxis yAxis
  x-z : DistinctAxis xAxis zAxis
  y-time : DistinctAxis yAxis timeAxis
  y-x : DistinctAxis yAxis xAxis
  y-z : DistinctAxis yAxis zAxis
  z-time : DistinctAxis zAxis timeAxis
  z-x : DistinctAxis zAxis xAxis
  z-y : DistinctAxis zAxis yAxis

infix 4 _≈Cl_
data _≈Cl_ : CliffordWord → CliffordWord → Set where
  cl-refl : ∀ {word} → word ≈Cl word
  cl-sym : ∀ {left right} → left ≈Cl right → right ≈Cl left
  cl-trans :
    ∀ {left middle right} →
    left ≈Cl middle → middle ≈Cl right → left ≈Cl right
  cl-cong-left :
    ∀ {left right suffix} →
    left ≈Cl right → (left ∙ suffix) ≈Cl (right ∙ suffix)
  cl-cong-right :
    ∀ {left right prefix} →
    left ≈Cl right → (prefix ∙ left) ≈Cl (prefix ∙ right)
  cl-assoc :
    ∀ left middle right →
    ((left ∙ middle) ∙ right) ≈Cl (left ∙ (middle ∙ right))
  cl-square :
    (axis : Axis4) →
    (generator axis ∙ generator axis)
      ≈Cl scalarWord (metricSquare axis)
  cl-anticommute :
    ∀ {left right} →
    DistinctAxis left right →
    (generator left ∙ generator right)
      ≈Cl
    (scalarWord negative ∙ (generator right ∙ generator left))

------------------------------------------------------------------------
-- Explicit finite basis.


data CliffordBlade16 : Set where
  blade1 : CliffordBlade16
  bladeT bladeX bladeY bladeZ : CliffordBlade16
  bladeTX bladeTY bladeTZ bladeXY bladeXZ bladeYZ : CliffordBlade16
  bladeTXY bladeTXZ bladeTYZ bladeXYZ : CliffordBlade16
  bladeTXYZ : CliffordBlade16


data Parity : Set where
  even : Parity
  odd : Parity

combineParity : Parity → Parity → Parity
combineParity even right = right
combineParity odd even = odd
combineParity odd odd = even

wordParity : CliffordWord → Parity
wordParity (scalarWord _) = even
wordParity (generator _) = odd
wordParity (left ∙ right) = combineParity (wordParity left) (wordParity right)

bladeParity : CliffordBlade16 → Parity
bladeParity blade1 = even
bladeParity bladeT = odd
bladeParity bladeX = odd
bladeParity bladeY = odd
bladeParity bladeZ = odd
bladeParity bladeTX = even
bladeParity bladeTY = even
bladeParity bladeTZ = even
bladeParity bladeXY = even
bladeParity bladeXZ = even
bladeParity bladeYZ = even
bladeParity bladeTXY = odd
bladeParity bladeTXZ = odd
bladeParity bladeTYZ = odd
bladeParity bladeXYZ = odd
bladeParity bladeTXYZ = even


data ReversionSign : Set where
  reversePositive : ReversionSign
  reverseNegative : ReversionSign

reversionSign : CliffordBlade16 → ReversionSign
reversionSign blade1 = reversePositive
reversionSign bladeT = reversePositive
reversionSign bladeX = reversePositive
reversionSign bladeY = reversePositive
reversionSign bladeZ = reversePositive
reversionSign bladeTX = reverseNegative
reversionSign bladeTY = reverseNegative
reversionSign bladeTZ = reverseNegative
reversionSign bladeXY = reverseNegative
reversionSign bladeXZ = reverseNegative
reversionSign bladeYZ = reverseNegative
reversionSign bladeTXY = reverseNegative
reversionSign bladeTXZ = reverseNegative
reversionSign bladeTYZ = reverseNegative
reversionSign bladeXYZ = reverseNegative
reversionSign bladeTXYZ = reversePositive

record EvenCliffordWord : Set where
  constructor even-word
  field
    word : CliffordWord
    parityProof : wordParity word ≡ even
open EvenCliffordWord public

twoGeneratorEven : (left right : Axis4) → EvenCliffordWord
twoGeneratorEven left right =
  even-word (generator left ∙ generator right) refl

------------------------------------------------------------------------
-- Pin and Spin as products of unit generators.


data UnitGenerator : Set where
  unitT unitX unitY unitZ : UnitGenerator

unitAxis : UnitGenerator → Axis4
unitAxis unitT = timeAxis
unitAxis unitX = xAxis
unitAxis unitY = yAxis
unitAxis unitZ = zAxis

wordOfUnits : List UnitGenerator → CliffordWord
wordOfUnits [] = scalarWord positive
wordOfUnits (unit ∷ rest) = generator (unitAxis unit) ∙ wordOfUnits rest

record PinElement : Set where
  constructor pin-element
  field
    generators : List UnitGenerator
open PinElement public

record SpinElement : Set where
  constructor spin-element
  field
    pin : PinElement
    evenReceipt : wordParity (wordOfUnits (generators pin)) ≡ even
open SpinElement public

spinIdentity : SpinElement
spinIdentity = spin-element (pin-element []) refl

spinXYRotorWord : SpinElement
spinXYRotorWord = spin-element (pin-element (unitX ∷ unitY ∷ [])) refl

spinTZRotorWord : SpinElement
spinTZRotorWord = spin-element (pin-element (unitT ∷ unitZ ∷ [])) refl

------------------------------------------------------------------------
-- Quotient and global cover authority payloads.

record CliffordQuotientCompletion : Set₁ where
  field
    quotientCarrier : Set
    quotientMap : CliffordWord → quotientCarrier
    relationSound :
      ∀ {left right} → left ≈Cl right → quotientMap left ≡ quotientMap right
    universalProperty : ProofTerms.CliffordUniversalProof
open CliffordQuotientCompletion public

record ConstructiveSpinCompletion : Set₁ where
  field
    cliffordQuotient : CliffordQuotientCompletion
    spinDoubleCover : ProofTerms.SpinDoubleCoverProof
    twistedAdjointPreservesMetric : Set
    evenSubalgebraClosedUnderProduct : Set
    reversionSuppliesInverseOnSpin : Set
open ConstructiveSpinCompletion public

constructiveCliffordScope : Set
constructiveCliffordScope = CliffordBlade16
