module DASHI.Moonshine.Monster3BFiniteHeisenbergGroupLawFrontierExact where

------------------------------------------------------------------------
-- FINITE HEISENBERG GROUP-LAW FRONTIER
--
-- Identity, concrete F3 algebra, six-coordinate dot bilinearity and the exact
-- 2-cocycle identity are now proved.  The remaining group-law work is the
-- final phase-expression normalization for associativity and the inverse law.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BF3AlgebraExact as F3
import DASHI.Moonshine.Monster3BFiniteHeisenbergDotBilinearityExact as Dot
import DASHI.Moonshine.Monster3BFiniteHeisenbergCocycleExact as Cocycle

plusRightZero : (a : Trit) → G._+3_ a zer ≡ a
plusRightZero = F3.plusRightZero

mulRightZero : (a : Trit) → H._*3_ a zer ≡ zer
mulRightZero neg = refl
mulRightZero zer = refl
mulRightZero pos = refl

addZeroLeft : (x : G.X6) → H.addX6 H.zeroX6 x ≡ x
addZeroLeft (G.x6 a b c d e f) = refl

addZeroRight : (x : G.X6) → H.addX6 x H.zeroX6 ≡ x
addZeroRight (G.x6 a b c d e f)
  rewrite plusRightZero a | plusRightZero b | plusRightZero c
        | plusRightZero d | plusRightZero e | plusRightZero f = refl

dotZeroLeft : (x : G.X6) → H.dot6 H.zeroX6 x ≡ zer
dotZeroLeft (G.x6 a b c d e f) = refl

dotZeroRight : (x : G.X6) → H.dot6 x H.zeroX6 ≡ zer
dotZeroRight (G.x6 a b c d e f)
  rewrite mulRightZero a | mulRightZero b | mulRightZero c
        | mulRightZero d | mulRightZero e | mulRightZero f = refl

leftIdentity : (g : H.Heisenberg6) → H.compose H.identityH g ≡ g
leftIdentity
  (H.heisenberg6 (H.symplectic12 x ξ) c)
  rewrite addZeroLeft x | addZeroLeft ξ | dotZeroLeft x
        | plusRightZero c = refl

rightIdentity : (g : H.Heisenberg6) → H.compose g H.identityH ≡ g
rightIdentity
  (H.heisenberg6 (H.symplectic12 x ξ) c)
  rewrite addZeroRight x | addZeroRight ξ | dotZeroRight ξ
        | plusRightZero c = refl

f3AssociativityAvailable : Bool
f3AssociativityAvailable = F3.additiveAssociativity F3.canonicalF3AlgebraBoundary

f3AssociativityAvailableIsTrue : f3AssociativityAvailable ≡ true
f3AssociativityAvailableIsTrue = refl

dotBilinearityAvailable : Bool
dotBilinearityAvailable = Dot.leftLinearityProved Dot.canonicalDotBilinearityBoundary

dotBilinearityAvailableIsTrue : dotBilinearityAvailable ≡ true
dotBilinearityAvailableIsTrue = refl

cocycleIdentityAvailable : Bool
cocycleIdentityAvailable = Cocycle.cocycleIdentityProved Cocycle.canonicalHeisenbergCocycleBoundary

cocycleIdentityAvailableIsTrue : cocycleIdentityAvailable ≡ true
cocycleIdentityAvailableIsTrue = refl

data GroupLawLeaf : Set where
  proveLeftIdentity : GroupLawLeaf
  proveRightIdentity : GroupLawLeaf
  proveF3Associativity : GroupLawLeaf
  proveDotBilinearity : GroupLawLeaf
  proveCocycleIdentity : GroupLawLeaf
  proveHeisenbergAssociativity : GroupLawLeaf
  proveInverseFormula : GroupLawLeaf

data LeafState : Set where closed open blocked : LeafState

leafState : GroupLawLeaf → LeafState
leafState proveLeftIdentity = closed
leafState proveRightIdentity = closed
leafState proveF3Associativity = closed
leafState proveDotBilinearity = closed
leafState proveCocycleIdentity = closed
leafState proveHeisenbergAssociativity = open
leafState proveInverseFormula = open

data Requires : GroupLawLeaf → GroupLawLeaf → Set where
  cocycleNeedsScalarAssociativity :
    Requires proveCocycleIdentity proveF3Associativity
  cocycleNeedsDotBilinearity :
    Requires proveCocycleIdentity proveDotBilinearity
  associativityNeedsCocycle :
    Requires proveHeisenbergAssociativity proveCocycleIdentity
  inverseNeedsScalarAssociativity :
    Requires proveInverseFormula proveF3Associativity
  inverseNeedsDotBilinearity :
    Requires proveInverseFormula proveDotBilinearity

highestImpactGroupLawLeaf : GroupLawLeaf
highestImpactGroupLawLeaf = proveHeisenbergAssociativity

highestImpactGroupLawLeafIsOpen : leafState highestImpactGroupLawLeaf ≡ open
highestImpactGroupLawLeafIsOpen = refl

record HeisenbergGroupLawFrontierBoundary : Set where
  constructor heisenbergGroupLawFrontierBoundary
  field
    leftIdentityProved : Bool
    rightIdentityProved : Bool
    scalarAssociativityProvedHere : Bool
    scalarDistributivityProvedHere : Bool
    dotBilinearityProvedHere : Bool
    cocycleIdentityProvedHere : Bool
    fullAssociativityProvedHere : Bool
    inverseLawProvedHere : Bool
open HeisenbergGroupLawFrontierBoundary public

canonicalHeisenbergGroupLawFrontierBoundary : HeisenbergGroupLawFrontierBoundary
canonicalHeisenbergGroupLawFrontierBoundary =
  heisenbergGroupLawFrontierBoundary true true true true true true false false
