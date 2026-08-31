module DASHI.Moonshine.Monster3BFiniteHeisenbergGroupLawFrontierExact where

------------------------------------------------------------------------
-- FINITE HEISENBERG GROUP-LAW FRONTIER
--
-- The central-extension multiplication is already constructed.  This owner
-- closes the identity laws and isolates the remaining associativity/inverse
-- work at the exact algebraic seams: F3 addition, dot-product bilinearity and
-- the resulting 2-cocycle identity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

------------------------------------------------------------------------
-- 1. Exact scalar identities needed by the identity laws.
------------------------------------------------------------------------

plusRightZero : (a : Trit) → G._+3_ a zer ≡ a
plusRightZero neg = refl
plusRightZero zer = refl
plusRightZero pos = refl

mulRightZero : (a : Trit) → H._*3_ a zer ≡ zer
mulRightZero neg = refl
mulRightZero zer = refl
mulRightZero pos = refl

------------------------------------------------------------------------
-- 2. Vector zero laws and vanishing cocycle legs.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 3. Both identity laws for the actual Heisenberg multiplication.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- 4. Remaining exact algebraic obligations.
--
-- Associativity is equivalent here to the standard cocycle identity
--
--   beta(g,h) + beta(g+h,k) = beta(h,k) + beta(g,h+k)
--
-- for beta((x,xi),(y,eta)) = xi . y.  Bilinearity of dot6 discharges that
-- identity.  The inverse formula then uses additive inverses plus the same
-- bilinearity.  Those facts are deliberately not replaced by booleans here.
------------------------------------------------------------------------

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
leafState proveF3Associativity = open
leafState proveDotBilinearity = open
leafState proveCocycleIdentity = blocked
leafState proveHeisenbergAssociativity = blocked
leafState proveInverseFormula = blocked

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

record HeisenbergGroupLawFrontierBoundary : Set where
  constructor heisenbergGroupLawFrontierBoundary
  field
    leftIdentityProved : Bool
    rightIdentityProved : Bool
    scalarAssociativityProvedHere : Bool
    dotBilinearityProvedHere : Bool
    cocycleIdentityProvedHere : Bool
    fullAssociativityProvedHere : Bool
    inverseLawProvedHere : Bool
open HeisenbergGroupLawFrontierBoundary public

canonicalHeisenbergGroupLawFrontierBoundary : HeisenbergGroupLawFrontierBoundary
canonicalHeisenbergGroupLawFrontierBoundary =
  heisenbergGroupLawFrontierBoundary true true false false false false false
