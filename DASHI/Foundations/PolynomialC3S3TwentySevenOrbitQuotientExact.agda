module DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact where

-- Exact 27 -> 11 -> 7 S3/C3 conjugacy quotient.
-- Classic normal-subgroup orbit theory. Reuse existing seven-shape owner.
-- This is NOT the free-output-phase 27 -> 9 = 2+7 quotient.
-- Source-written / kernel-pending, no geometry/Monster equality.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import Base369 as Base
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitRefinementExact as Act

Code27 : Set
Code27 = Tower.LevelTwoCode

data Orbit11 : Set where
  identityOrbit
  cycleForwardOrbit
  cycleBackwardOrbit
  transpositionOrbit
  constantOrbit
  rank2OneFixedA
  rank2OneFixedB
  rank2TwoFixedA
  rank2TwoFixedB
  rank2TwoCycleA
  rank2TwoCycleB : Orbit11

classify11 : Code27 → Orbit11
classify11 (Base.tri-low , (Base.tri-low , Base.tri-low)) = constantOrbit
classify11 (Base.tri-low , (Base.tri-low , Base.tri-mid)) = rank2OneFixedA
classify11 (Base.tri-low , (Base.tri-low , Base.tri-high)) = rank2TwoFixedA
classify11 (Base.tri-low , (Base.tri-mid , Base.tri-low)) = rank2TwoFixedB
classify11 (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = rank2TwoFixedA
classify11 (Base.tri-low , (Base.tri-mid , Base.tri-high)) = identityOrbit
classify11 (Base.tri-low , (Base.tri-high , Base.tri-low)) = rank2OneFixedB
classify11 (Base.tri-low , (Base.tri-high , Base.tri-mid)) = transpositionOrbit
classify11 (Base.tri-low , (Base.tri-high , Base.tri-high)) = rank2TwoFixedB
classify11 (Base.tri-mid , (Base.tri-low , Base.tri-low)) = rank2TwoCycleA
classify11 (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = rank2TwoCycleB
classify11 (Base.tri-mid , (Base.tri-low , Base.tri-high)) = transpositionOrbit
classify11 (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = rank2OneFixedB
classify11 (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = constantOrbit
classify11 (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = rank2TwoFixedB
classify11 (Base.tri-mid , (Base.tri-high , Base.tri-low)) = cycleForwardOrbit
classify11 (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = rank2TwoCycleA
classify11 (Base.tri-mid , (Base.tri-high , Base.tri-high)) = rank2OneFixedB
classify11 (Base.tri-high , (Base.tri-low , Base.tri-low)) = rank2TwoCycleB
classify11 (Base.tri-high , (Base.tri-low , Base.tri-mid)) = cycleBackwardOrbit
classify11 (Base.tri-high , (Base.tri-low , Base.tri-high)) = rank2OneFixedA
classify11 (Base.tri-high , (Base.tri-mid , Base.tri-low)) = transpositionOrbit
classify11 (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = rank2OneFixedA
classify11 (Base.tri-high , (Base.tri-mid , Base.tri-high)) = rank2TwoFixedA
classify11 (Base.tri-high , (Base.tri-high , Base.tri-low)) = rank2TwoCycleA
classify11 (Base.tri-high , (Base.tri-high , Base.tri-mid)) = rank2TwoCycleB
classify11 (Base.tri-high , (Base.tri-high , Base.tri-high)) = constantOrbit

representative11 : Orbit11 → Code27
representative11 identityOrbit = Base.tri-low , (Base.tri-mid , Base.tri-high)
representative11 cycleForwardOrbit = Base.tri-mid , (Base.tri-high , Base.tri-low)
representative11 cycleBackwardOrbit = Base.tri-high , (Base.tri-low , Base.tri-mid)
representative11 transpositionOrbit = Base.tri-low , (Base.tri-high , Base.tri-mid)
representative11 constantOrbit = Base.tri-low , (Base.tri-low , Base.tri-low)
representative11 rank2OneFixedA = Base.tri-low , (Base.tri-low , Base.tri-mid)
representative11 rank2OneFixedB = Base.tri-low , (Base.tri-high , Base.tri-low)
representative11 rank2TwoFixedA = Base.tri-low , (Base.tri-low , Base.tri-high)
representative11 rank2TwoFixedB = Base.tri-low , (Base.tri-mid , Base.tri-low)
representative11 rank2TwoCycleA = Base.tri-mid , (Base.tri-low , Base.tri-low)
representative11 rank2TwoCycleB = Base.tri-mid , (Base.tri-low , Base.tri-mid)

classifyRepresentative11 : (o : Orbit11) → classify11 (representative11 o) ≡ o
classifyRepresentative11 identityOrbit = refl
classifyRepresentative11 cycleForwardOrbit = refl
classifyRepresentative11 cycleBackwardOrbit = refl
classifyRepresentative11 transpositionOrbit = refl
classifyRepresentative11 constantOrbit = refl
classifyRepresentative11 rank2OneFixedA = refl
classifyRepresentative11 rank2OneFixedB = refl
classifyRepresentative11 rank2TwoFixedA = refl
classifyRepresentative11 rank2TwoFixedB = refl
classifyRepresentative11 rank2TwoCycleA = refl
classifyRepresentative11 rank2TwoCycleB = refl

data Rotation3 : Set where
  phaseZero phaseOne phaseTwo : Rotation3

actRotation3 : Rotation3 → Code27 → Code27
actRotation3 phaseZero x = x
actRotation3 phaseOne x = Act.cycleCode x
actRotation3 phaseTwo x = Act.cycleCode (Act.cycleCode x)

rotationToRepresentative : Code27 → Rotation3
rotationToRepresentative (Base.tri-low , (Base.tri-low , Base.tri-low)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-low , Base.tri-mid)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-low , Base.tri-high)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-low)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = phaseOne
rotationToRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-high)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-high , Base.tri-low)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-high , Base.tri-mid)) = phaseZero
rotationToRepresentative (Base.tri-low , (Base.tri-high , Base.tri-high)) = phaseTwo
rotationToRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-low)) = phaseZero
rotationToRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = phaseZero
rotationToRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-high)) = phaseTwo
rotationToRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = phaseOne
rotationToRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = phaseOne
rotationToRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = phaseOne
rotationToRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-low)) = phaseZero
rotationToRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = phaseOne
rotationToRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-high)) = phaseTwo
rotationToRepresentative (Base.tri-high , (Base.tri-low , Base.tri-low)) = phaseTwo
rotationToRepresentative (Base.tri-high , (Base.tri-low , Base.tri-mid)) = phaseZero
rotationToRepresentative (Base.tri-high , (Base.tri-low , Base.tri-high)) = phaseTwo
rotationToRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-low)) = phaseOne
rotationToRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = phaseOne
rotationToRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-high)) = phaseTwo
rotationToRepresentative (Base.tri-high , (Base.tri-high , Base.tri-low)) = phaseTwo
rotationToRepresentative (Base.tri-high , (Base.tri-high , Base.tri-mid)) = phaseOne
rotationToRepresentative (Base.tri-high , (Base.tri-high , Base.tri-high)) = phaseTwo

codeFromClassRepresentative :
  (x : Code27) →
  x ≡ actRotation3 (rotationToRepresentative x) (representative11 (classify11 x))
codeFromClassRepresentative (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
codeFromClassRepresentative (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

classify11CycleInvariant : (x : Code27) →
  classify11 (Act.cycleCode x) ≡ classify11 x
classify11CycleInvariant (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classify11CycleInvariant (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

reflectionOn11 : Orbit11 → Orbit11
reflectionOn11 identityOrbit = identityOrbit
reflectionOn11 cycleForwardOrbit = cycleBackwardOrbit
reflectionOn11 cycleBackwardOrbit = cycleForwardOrbit
reflectionOn11 transpositionOrbit = transpositionOrbit
reflectionOn11 constantOrbit = constantOrbit
reflectionOn11 rank2OneFixedA = rank2OneFixedB
reflectionOn11 rank2OneFixedB = rank2OneFixedA
reflectionOn11 rank2TwoFixedA = rank2TwoFixedB
reflectionOn11 rank2TwoFixedB = rank2TwoFixedA
reflectionOn11 rank2TwoCycleA = rank2TwoCycleB
reflectionOn11 rank2TwoCycleB = rank2TwoCycleA

reflection11Involutive : (o : Orbit11) →
  reflectionOn11 (reflectionOn11 o) ≡ o
reflection11Involutive identityOrbit = refl
reflection11Involutive cycleForwardOrbit = refl
reflection11Involutive cycleBackwardOrbit = refl
reflection11Involutive transpositionOrbit = refl
reflection11Involutive constantOrbit = refl
reflection11Involutive rank2OneFixedA = refl
reflection11Involutive rank2OneFixedB = refl
reflection11Involutive rank2TwoFixedA = refl
reflection11Involutive rank2TwoFixedB = refl
reflection11Involutive rank2TwoCycleA = refl
reflection11Involutive rank2TwoCycleB = refl

reflectionClassifies : (x : Code27) →
  classify11 (Act.reflectionCode x) ≡ reflectionOn11 (classify11 x)
reflectionClassifies (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
reflectionClassifies (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

mergeToSeven : Orbit11 → Shape.ShapeOrbit7
mergeToSeven identityOrbit = Shape.identityShape
mergeToSeven cycleForwardOrbit = Shape.threeCycleShape
mergeToSeven cycleBackwardOrbit = Shape.threeCycleShape
mergeToSeven transpositionOrbit = Shape.transpositionShape
mergeToSeven constantOrbit = Shape.constantShape
mergeToSeven rank2OneFixedA = Shape.rank2OneFixedShape
mergeToSeven rank2OneFixedB = Shape.rank2OneFixedShape
mergeToSeven rank2TwoFixedA = Shape.rank2TwoFixedShape
mergeToSeven rank2TwoFixedB = Shape.rank2TwoFixedShape
mergeToSeven rank2TwoCycleA = Shape.rank2TwoCycleShape
mergeToSeven rank2TwoCycleB = Shape.rank2TwoCycleShape

classificationFactors : (x : Code27) →
  Shape.shapeClass x ≡ mergeToSeven (classify11 x)
classificationFactors (Base.tri-low , (Base.tri-low , Base.tri-low)) = refl
classificationFactors (Base.tri-low , (Base.tri-low , Base.tri-mid)) = refl
classificationFactors (Base.tri-low , (Base.tri-low , Base.tri-high)) = refl
classificationFactors (Base.tri-low , (Base.tri-mid , Base.tri-low)) = refl
classificationFactors (Base.tri-low , (Base.tri-mid , Base.tri-mid)) = refl
classificationFactors (Base.tri-low , (Base.tri-mid , Base.tri-high)) = refl
classificationFactors (Base.tri-low , (Base.tri-high , Base.tri-low)) = refl
classificationFactors (Base.tri-low , (Base.tri-high , Base.tri-mid)) = refl
classificationFactors (Base.tri-low , (Base.tri-high , Base.tri-high)) = refl
classificationFactors (Base.tri-mid , (Base.tri-low , Base.tri-low)) = refl
classificationFactors (Base.tri-mid , (Base.tri-low , Base.tri-mid)) = refl
classificationFactors (Base.tri-mid , (Base.tri-low , Base.tri-high)) = refl
classificationFactors (Base.tri-mid , (Base.tri-mid , Base.tri-low)) = refl
classificationFactors (Base.tri-mid , (Base.tri-mid , Base.tri-mid)) = refl
classificationFactors (Base.tri-mid , (Base.tri-mid , Base.tri-high)) = refl
classificationFactors (Base.tri-mid , (Base.tri-high , Base.tri-low)) = refl
classificationFactors (Base.tri-mid , (Base.tri-high , Base.tri-mid)) = refl
classificationFactors (Base.tri-mid , (Base.tri-high , Base.tri-high)) = refl
classificationFactors (Base.tri-high , (Base.tri-low , Base.tri-low)) = refl
classificationFactors (Base.tri-high , (Base.tri-low , Base.tri-mid)) = refl
classificationFactors (Base.tri-high , (Base.tri-low , Base.tri-high)) = refl
classificationFactors (Base.tri-high , (Base.tri-mid , Base.tri-low)) = refl
classificationFactors (Base.tri-high , (Base.tri-mid , Base.tri-mid)) = refl
classificationFactors (Base.tri-high , (Base.tri-mid , Base.tri-high)) = refl
classificationFactors (Base.tri-high , (Base.tri-high , Base.tri-low)) = refl
classificationFactors (Base.tri-high , (Base.tri-high , Base.tri-mid)) = refl
classificationFactors (Base.tri-high , (Base.tri-high , Base.tri-high)) = refl

mergeIgnoresReflection : (o : Orbit11) →
  mergeToSeven (reflectionOn11 o) ≡ mergeToSeven o
mergeIgnoresReflection identityOrbit = refl
mergeIgnoresReflection cycleForwardOrbit = refl
mergeIgnoresReflection cycleBackwardOrbit = refl
mergeIgnoresReflection transpositionOrbit = refl
mergeIgnoresReflection constantOrbit = refl
mergeIgnoresReflection rank2OneFixedA = refl
mergeIgnoresReflection rank2OneFixedB = refl
mergeIgnoresReflection rank2TwoFixedA = refl
mergeIgnoresReflection rank2TwoFixedB = refl
mergeIgnoresReflection rank2TwoCycleA = refl
mergeIgnoresReflection rank2TwoCycleB = refl

allEleven : List Orbit11
allEleven = identityOrbit
  ∷ cycleForwardOrbit
  ∷ cycleBackwardOrbit
  ∷ transpositionOrbit
  ∷ constantOrbit
  ∷ rank2OneFixedA
  ∷ rank2OneFixedB
  ∷ rank2TwoFixedA
  ∷ rank2TwoFixedB
  ∷ rank2TwoCycleA
  ∷ rank2TwoCycleB ∷ []

countEleven : Shape.listCount allEleven ≡ 11
countEleven = refl

-- True orbit equivalence, not just numeric class labels.
classifyRotationInvariant :
  (rot : Rotation3) (x : Code27) →
  classify11 (actRotation3 rot x) ≡ classify11 x
classifyRotationInvariant phaseZero x = refl
classifyRotationInvariant phaseOne x = classify11CycleInvariant x
classifyRotationInvariant phaseTwo x =
  trans (classify11CycleInvariant (Act.cycleCode x)) (classify11CycleInvariant x)

minusRotation : Rotation3 → Rotation3 → Rotation3
minusRotation phaseZero phaseZero = phaseZero
minusRotation phaseZero phaseOne = phaseTwo
minusRotation phaseZero phaseTwo = phaseOne
minusRotation phaseOne phaseZero = phaseOne
minusRotation phaseOne phaseOne = phaseZero
minusRotation phaseOne phaseTwo = phaseTwo
minusRotation phaseTwo phaseZero = phaseTwo
minusRotation phaseTwo phaseOne = phaseOne
minusRotation phaseTwo phaseTwo = phaseZero

rotationDifferenceCancel :
  (a b : Rotation3) (x : Code27) →
  actRotation3 (minusRotation a b) (actRotation3 b x) ≡ actRotation3 a x
rotationDifferenceCancel phaseZero phaseZero x = refl
rotationDifferenceCancel phaseZero phaseOne x = Act.cycleCodeThreeTimes x
rotationDifferenceCancel phaseZero phaseTwo x = Act.cycleCodeThreeTimes x
rotationDifferenceCancel phaseOne phaseZero x = refl
rotationDifferenceCancel phaseOne phaseOne x = refl
rotationDifferenceCancel phaseOne phaseTwo x =
  cong Act.cycleCode (Act.cycleCodeThreeTimes x)
rotationDifferenceCancel phaseTwo phaseZero x = refl
rotationDifferenceCancel phaseTwo phaseOne x = refl
rotationDifferenceCancel phaseTwo phaseTwo x = refl

C3Related : Code27 → Code27 → Set
C3Related x y = Σ Rotation3 (λ rot → x ≡ actRotation3 rot y)

relatedHasSameClass : (x y : Code27) →
  C3Related x y → classify11 x ≡ classify11 y
relatedHasSameClass x y (rot , eq) =
  trans (cong classify11 eq) (classifyRotationInvariant rot y)

sameClassHasRotation : (x y : Code27) →
  classify11 x ≡ classify11 y → C3Related x y
sameClassHasRotation x y eq =
  minusRotation (rotationToRepresentative x) (rotationToRepresentative y) ,
  trans (codeFromClassRepresentative x)
    (trans (cong (λ o → actRotation3 (rotationToRepresentative x)
                 (representative11 o)) eq)
      (sym (trans (cong (actRotation3
                    (minusRotation (rotationToRepresentative x)
                                   (rotationToRepresentative y)))
                        (codeFromClassRepresentative y))
                  (rotationDifferenceCancel
                    (rotationToRepresentative x) (rotationToRepresentative y)
                    (representative11 (classify11 y))))))

Field27 : Set
Field27 = Code27 → Base.TriTruth

Field11 : Set
Field11 = Orbit11 → Base.TriTruth

Field7 : Set
Field7 = Shape.ShapeOrbit7 → Base.TriTruth

inflate11 : Field11 → Field27
inflate11 f x = f (classify11 x)

inflate7 : Field7 → Field11
inflate7 f o = f (mergeToSeven o)

inflate7To27 : Field7 → Field27
inflate7To27 f x = f (Shape.shapeClass x)

pullbackComposes :
  (f : Field7) (x : Code27) →
  inflate11 (inflate7 f) x ≡ inflate7To27 f x
pullbackComposes f x = cong f (sym (classificationFactors x))

mergeRepresentative7 : (shape : Shape.ShapeOrbit7) →
  mergeToSeven (classify11 (Shape.shapeRepresentative shape)) ≡ shape
mergeRepresentative7 shape =
  trans (sym (classificationFactors (Shape.shapeRepresentative shape)))
    (Shape.representativeHasDeclaredShape shape)

inflate11InjectiveAt :
  (f g : Field11) →
  ((x : Code27) → inflate11 f x ≡ inflate11 g x) →
  (o : Orbit11) → f o ≡ g o
inflate11InjectiveAt f g eq o =
  trans (sym (cong f (classifyRepresentative11 o)))
    (trans (eq (representative11 o))
      (cong g (classifyRepresentative11 o)))

inflate7InjectiveAt :
  (f g : Field7) →
  ((o : Orbit11) → inflate7 f o ≡ inflate7 g o) →
  (s : Shape.ShapeOrbit7) → f s ≡ g s
inflate7InjectiveAt f g eq s =
  trans (sym (cong f (mergeRepresentative7 s)))
    (trans (eq (classify11 (Shape.shapeRepresentative s)))
      (cong g (mergeRepresentative7 s)))

inflate11C3Invariant :
  (f : Field11) (x : Code27) →
  inflate11 f (Act.cycleCode x) ≡ inflate11 f x
inflate11C3Invariant f x = cong f (classify11CycleInvariant x)

inflate11ReflectionCovariant :
  (f : Field11) (x : Code27) →
  inflate11 f (Act.reflectionCode x)
    ≡ f (reflectionOn11 (classify11 x))
inflate11ReflectionCovariant f x = cong f (reflectionClassifies x)

rotationPreservesInvariant :
  (f : Field27) →
  ((x : Code27) → f (Act.cycleCode x) ≡ f x) →
  (rot : Rotation3) (x : Code27) →
  f (actRotation3 rot x) ≡ f x
rotationPreservesInvariant f inv phaseZero x = refl
rotationPreservesInvariant f inv phaseOne x = inv x
rotationPreservesInvariant f inv phaseTwo x =
  trans (inv (Act.cycleCode x)) (inv x)

everyC3InvariantFieldDescends :
  (f : Field27) →
  ((x : Code27) → f (Act.cycleCode x) ≡ f x) →
  (x : Code27) →
  f x ≡ inflate11 (λ o → f (representative11 o)) x
everyC3InvariantFieldDescends f inv x =
  trans (cong f (codeFromClassRepresentative x))
    (rotationPreservesInvariant f inv
      (rotationToRepresentative x) (representative11 (classify11 x)))
