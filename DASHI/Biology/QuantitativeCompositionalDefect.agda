module DASHI.Biology.QuantitativeCompositionalDefect where

open import DASHI.Core.Prelude

import DASHI.Biology.ProductiveTransformCoherence as Coherence
import DASHI.Biology.StateDependentMultiplexTransducer as Stateful

------------------------------------------------------------------------
-- Quantitative compositional defect.
--
-- Exact commutation is the zero-defect case.  Nonzero defect is typed by its
-- role so productive opposition is not silently identified with destructive
-- incompatibility.  This finite Nat-valued core is deliberately constructive;
-- later analytic consumers may replace Nat by Bishop reals or another ordered
-- additive carrier.
--
-- Source-facing references:
-- Giovanni Petri et al., "Homological scaffolds of brain functional
-- networks", DOI 10.1098/rsif.2014.0873.
-- J. A. Scott Kelso, "Multistability and metastability: understanding
-- dynamic coordination in the brain", DOI 10.1098/rstb.2011.0351.

data DefectKind : Set where
  commutingDefect : DefectKind
  unresolvedResidual : DefectKind
  destructiveIncompatibility : DefectKind
  productiveOpposition : DefectKind
  orderResidual : DefectKind

record TypedDefect : Set where
  constructor typedDefect
  field
    kind : DefectKind
    magnitude : Nat
    weight : Nat

open TypedDefect public

weightedMagnitude : TypedDefect → Nat
weightedMagnitude d = weight d * magnitude d

totalDefect : List TypedDefect → Nat
totalDefect [] = zero
totalDefect (d ∷ ds) = weightedMagnitude d + totalDefect ds

incompatibleCharge : TypedDefect → Nat
incompatibleCharge (typedDefect destructiveIncompatibility m w) = w * m
incompatibleCharge _ = zero

unresolvedCharge : TypedDefect → Nat
unresolvedCharge (typedDefect unresolvedResidual m w) = w * m
unresolvedCharge (typedDefect orderResidual m w) = w * m
unresolvedCharge _ = zero

productiveCredit : TypedDefect → Nat
productiveCredit (typedDefect productiveOpposition m w) = w * m
productiveCredit _ = zero

sumIncompatible : List TypedDefect → Nat
sumIncompatible [] = zero
sumIncompatible (d ∷ ds) = incompatibleCharge d + sumIncompatible ds

sumUnresolved : List TypedDefect → Nat
sumUnresolved [] = zero
sumUnresolved (d ∷ ds) = unresolvedCharge d + sumUnresolved ds

sumProductive : List TypedDefect → Nat
sumProductive [] = zero
sumProductive (d ∷ ds) = productiveCredit d + sumProductive ds

netDefect : List TypedDefect → Nat
netDefect ds =
  (sumIncompatible ds + sumUnresolved ds) ∸ sumProductive ds

------------------------------------------------------------------------
-- Finite triangle/cycle surfaces.

record QuantitativeTriangle : Set₁ where
  field
    Carrier : Set
    direct : Carrier → Carrier
    first : Carrier → Carrier
    second : Carrier → Carrier
    distance : Carrier → Carrier → Nat
    witness : Carrier

open QuantitativeTriangle public

triangleDefect : QuantitativeTriangle → Nat
triangleDefect T =
  distance T
    (direct T (witness T))
    (second T (first T (witness T)))

boolDistance : Bool → Bool → Nat
boolDistance false false = zero
boolDistance true true = zero
boolDistance _ _ = suc zero

canonicalZeroDefectTriangle : QuantitativeTriangle
canonicalZeroDefectTriangle =
  record
    { Carrier = Bool
    ; direct = Coherence.identity
    ; first = λ x → x
    ; second = λ x → x
    ; distance = boolDistance
    ; witness = false
    }

canonicalZeroDefectIsZero :
  triangleDefect canonicalZeroDefectTriangle ≡ zero
canonicalZeroDefectIsZero = refl

canonicalOrderTriangle : QuantitativeTriangle
canonicalOrderTriangle =
  record
    { Carrier = Bool
    ; direct = Coherence.inhibitThenSaturate
    ; first = Coherence.setTrue
    ; second = Stateful.boolNot
    ; distance = boolDistance
    ; witness = false
    }

canonicalOrderTriangleDefectIsOne :
  triangleDefect canonicalOrderTriangle ≡ suc zero
canonicalOrderTriangleDefectIsOne = refl

------------------------------------------------------------------------
-- Productive opposition is tracked separately from incompatibility.

zeroTypedDefect : TypedDefect
zeroTypedDefect = typedDefect commutingDefect zero (suc zero)

productiveTypedDefect : TypedDefect
productiveTypedDefect = typedDefect productiveOpposition (suc zero) (suc zero)

destructiveTypedDefect : TypedDefect
destructiveTypedDefect =
  typedDefect destructiveIncompatibility (suc (suc zero)) (suc zero)

orderTypedDefect : TypedDefect
orderTypedDefect = typedDefect orderResidual (suc zero) (suc zero)

canonicalDefectAtlas : List TypedDefect
canonicalDefectAtlas =
  zeroTypedDefect
  ∷ destructiveTypedDefect
  ∷ orderTypedDefect
  ∷ productiveTypedDefect
  ∷ []

canonicalTotalDefectIsFour :
  totalDefect canonicalDefectAtlas ≡ 4
canonicalTotalDefectIsFour = refl

canonicalNetDefectIsTwo :
  netDefect canonicalDefectAtlas ≡ 2
canonicalNetDefectIsTwo = refl

------------------------------------------------------------------------
-- Extension/restriction witnesses.

baseCoalitionDefects : List TypedDefect
baseCoalitionDefects = destructiveTypedDefect ∷ []

extendedCoalitionDefects : List TypedDefect
extendedCoalitionDefects =
  destructiveTypedDefect ∷ productiveTypedDefect ∷ []

baseNetDefectIsTwo :
  netDefect baseCoalitionDefects ≡ 2
baseNetDefectIsTwo = refl

productiveExtensionNetDefectIsOne :
  netDefect extendedCoalitionDefects ≡ 1
productiveExtensionNetDefectIsOne = refl

productiveExtensionReducesNetDefect :
  netDefect extendedCoalitionDefects ≤ netDefect baseCoalitionDefects
productiveExtensionReducesNetDefect = s≤s z≤n

record QuantitativeDefectBoundary : Set where
  constructor quantitativeDefectBoundary
  field
    allNoncommutationIsError : Bool
    allNoncommutationIsErrorIsFalse : allNoncommutationIsError ≡ false

    allInhibitionIsDestructive : Bool
    allInhibitionIsDestructiveIsFalse : allInhibitionIsDestructive ≡ false

    natDefectIsBiologicalMeasurement : Bool
    natDefectIsBiologicalMeasurementIsFalse :
      natDefectIsBiologicalMeasurement ≡ false

canonicalQuantitativeDefectBoundary : QuantitativeDefectBoundary
canonicalQuantitativeDefectBoundary =
  quantitativeDefectBoundary false refl false refl false refl
