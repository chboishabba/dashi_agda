module DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact where

------------------------------------------------------------------------
-- FINITE HEISENBERG CENTRAL-EXTENSION CARRIER ON F_3^6
--
-- This owner advances the Stone-von Neumann frontier from the 36 local Weyl
-- generator relations to an explicit global coordinate carrier
--
--   H_6 = X_6 x X_6^* x F_3
--
-- with the standard Heisenberg cocycle and alternating commutator pairing.
--
-- It deliberately does NOT yet claim the full group laws or finite
-- Stone-von Neumann uniqueness.  Those remain separate theorem obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G

------------------------------------------------------------------------
-- 1. F_3 scalar multiplication and the six-coordinate dot pairing.
------------------------------------------------------------------------

infixl 7 _*3_

_*3_ : Trit → Trit → Trit
zer *3 b = zer
pos *3 b = b
neg *3 neg = pos
neg *3 zer = zer
neg *3 pos = neg

zeroX6 : G.X6
zeroX6 = G.x6 zer zer zer zer zer zer

basis : G.Axis6 → G.X6
basis G.axis0 = G.x6 pos zer zer zer zer zer
basis G.axis1 = G.x6 zer pos zer zer zer zer
basis G.axis2 = G.x6 zer zer pos zer zer zer
basis G.axis3 = G.x6 zer zer zer pos zer zer
basis G.axis4 = G.x6 zer zer zer zer pos zer
basis G.axis5 = G.x6 zer zer zer zer zer pos

addX6 : G.X6 → G.X6 → G.X6
addX6 a b =
  G.x6
    (G._+3_ (G.x0 a) (G.x0 b))
    (G._+3_ (G.x1 a) (G.x1 b))
    (G._+3_ (G.x2 a) (G.x2 b))
    (G._+3_ (G.x3 a) (G.x3 b))
    (G._+3_ (G.x4 a) (G.x4 b))
    (G._+3_ (G.x5 a) (G.x5 b))

negX6 : G.X6 → G.X6
negX6 a =
  G.x6
    (G.negate3 (G.x0 a))
    (G.negate3 (G.x1 a))
    (G.negate3 (G.x2 a))
    (G.negate3 (G.x3 a))
    (G.negate3 (G.x4 a))
    (G.negate3 (G.x5 a))

dot6 : G.X6 → G.X6 → Trit
dot6 a b =
  G._+3_
    ((G.x0 a) *3 (G.x0 b))
    (G._+3_
      ((G.x1 a) *3 (G.x1 b))
      (G._+3_
        ((G.x2 a) *3 (G.x2 b))
        (G._+3_
          ((G.x3 a) *3 (G.x3 b))
          (G._+3_
            ((G.x4 a) *3 (G.x4 b))
            ((G.x5 a) *3 (G.x5 b))))))

dotBasisKronecker :
  (i j : G.Axis6) → dot6 (basis i) (basis j) ≡ G.kronecker i j
dotBasisKronecker G.axis0 G.axis0 = refl
dotBasisKronecker G.axis0 G.axis1 = refl
dotBasisKronecker G.axis0 G.axis2 = refl
dotBasisKronecker G.axis0 G.axis3 = refl
dotBasisKronecker G.axis0 G.axis4 = refl
dotBasisKronecker G.axis0 G.axis5 = refl
dotBasisKronecker G.axis1 G.axis0 = refl
dotBasisKronecker G.axis1 G.axis1 = refl
dotBasisKronecker G.axis1 G.axis2 = refl
dotBasisKronecker G.axis1 G.axis3 = refl
dotBasisKronecker G.axis1 G.axis4 = refl
dotBasisKronecker G.axis1 G.axis5 = refl
dotBasisKronecker G.axis2 G.axis0 = refl
dotBasisKronecker G.axis2 G.axis1 = refl
dotBasisKronecker G.axis2 G.axis2 = refl
dotBasisKronecker G.axis2 G.axis3 = refl
dotBasisKronecker G.axis2 G.axis4 = refl
dotBasisKronecker G.axis2 G.axis5 = refl
dotBasisKronecker G.axis3 G.axis0 = refl
dotBasisKronecker G.axis3 G.axis1 = refl
dotBasisKronecker G.axis3 G.axis2 = refl
dotBasisKronecker G.axis3 G.axis3 = refl
dotBasisKronecker G.axis3 G.axis4 = refl
dotBasisKronecker G.axis3 G.axis5 = refl
dotBasisKronecker G.axis4 G.axis0 = refl
dotBasisKronecker G.axis4 G.axis1 = refl
dotBasisKronecker G.axis4 G.axis2 = refl
dotBasisKronecker G.axis4 G.axis3 = refl
dotBasisKronecker G.axis4 G.axis4 = refl
dotBasisKronecker G.axis4 G.axis5 = refl
dotBasisKronecker G.axis5 G.axis0 = refl
dotBasisKronecker G.axis5 G.axis1 = refl
dotBasisKronecker G.axis5 G.axis2 = refl
dotBasisKronecker G.axis5 G.axis3 = refl
dotBasisKronecker G.axis5 G.axis4 = refl
dotBasisKronecker G.axis5 G.axis5 = refl

basisSelfPairIsNonzero : (i : G.Axis6) → dot6 (basis i) (basis i) ≡ pos
basisSelfPairIsNonzero G.axis0 = refl
basisSelfPairIsNonzero G.axis1 = refl
basisSelfPairIsNonzero G.axis2 = refl
basisSelfPairIsNonzero G.axis3 = refl
basisSelfPairIsNonzero G.axis4 = refl
basisSelfPairIsNonzero G.axis5 = refl

------------------------------------------------------------------------
-- 2. Twelve-dimensional quotient carrier X_6 + X_6^* and its alternating
--    symplectic form.
------------------------------------------------------------------------

record Symplectic12 : Set where
  constructor symplectic12
  field
    translationPart : G.X6
    modulationPart : G.X6
open Symplectic12 public

symplecticPair : Symplectic12 → Symplectic12 → Trit
symplecticPair u v =
  G._+3_
    (dot6 (translationPart u) (modulationPart v))
    (G.negate3 (dot6 (translationPart v) (modulationPart u)))

translationBasis : G.Axis6 → Symplectic12
translationBasis i = symplectic12 (basis i) zeroX6

modulationBasis : G.Axis6 → Symplectic12
modulationBasis i = symplectic12 zeroX6 (basis i)

translationModulationPair :
  (i j : G.Axis6) →
  symplecticPair (translationBasis i) (modulationBasis j)
  ≡ G.kronecker i j
translationModulationPair G.axis0 G.axis0 = refl
translationModulationPair G.axis0 G.axis1 = refl
translationModulationPair G.axis0 G.axis2 = refl
translationModulationPair G.axis0 G.axis3 = refl
translationModulationPair G.axis0 G.axis4 = refl
translationModulationPair G.axis0 G.axis5 = refl
translationModulationPair G.axis1 G.axis0 = refl
translationModulationPair G.axis1 G.axis1 = refl
translationModulationPair G.axis1 G.axis2 = refl
translationModulationPair G.axis1 G.axis3 = refl
translationModulationPair G.axis1 G.axis4 = refl
translationModulationPair G.axis1 G.axis5 = refl
translationModulationPair G.axis2 G.axis0 = refl
translationModulationPair G.axis2 G.axis1 = refl
translationModulationPair G.axis2 G.axis2 = refl
translationModulationPair G.axis2 G.axis3 = refl
translationModulationPair G.axis2 G.axis4 = refl
translationModulationPair G.axis2 G.axis5 = refl
translationModulationPair G.axis3 G.axis0 = refl
translationModulationPair G.axis3 G.axis1 = refl
translationModulationPair G.axis3 G.axis2 = refl
translationModulationPair G.axis3 G.axis3 = refl
translationModulationPair G.axis3 G.axis4 = refl
translationModulationPair G.axis3 G.axis5 = refl
translationModulationPair G.axis4 G.axis0 = refl
translationModulationPair G.axis4 G.axis1 = refl
translationModulationPair G.axis4 G.axis2 = refl
translationModulationPair G.axis4 G.axis3 = refl
translationModulationPair G.axis4 G.axis4 = refl
translationModulationPair G.axis4 G.axis5 = refl
translationModulationPair G.axis5 G.axis0 = refl
translationModulationPair G.axis5 G.axis1 = refl
translationModulationPair G.axis5 G.axis2 = refl
translationModulationPair G.axis5 G.axis3 = refl
translationModulationPair G.axis5 G.axis4 = refl
translationModulationPair G.axis5 G.axis5 = refl

canonicalBasisPairIsNontrivial :
  (i : G.Axis6) →
  symplecticPair (translationBasis i) (modulationBasis i) ≡ pos
canonicalBasisPairIsNontrivial G.axis0 = refl
canonicalBasisPairIsNontrivial G.axis1 = refl
canonicalBasisPairIsNontrivial G.axis2 = refl
canonicalBasisPairIsNontrivial G.axis3 = refl
canonicalBasisPairIsNontrivial G.axis4 = refl
canonicalBasisPairIsNontrivial G.axis5 = refl

------------------------------------------------------------------------
-- 3. Explicit central-extension carrier and standard Heisenberg cocycle.
------------------------------------------------------------------------

record Heisenberg6 : Set where
  constructor heisenberg6
  field
    quotient : Symplectic12
    centralPhase : Trit
open Heisenberg6 public

compose : Heisenberg6 → Heisenberg6 → Heisenberg6
compose g h =
  heisenberg6
    (symplectic12
      (addX6 (translationPart (quotient g)) (translationPart (quotient h)))
      (addX6 (modulationPart (quotient g)) (modulationPart (quotient h))))
    (G._+3_
      (centralPhase g)
      (G._+3_
        (centralPhase h)
        (dot6 (modulationPart (quotient g))
              (translationPart (quotient h)))))

identityH : Heisenberg6
identityH = heisenberg6 (symplectic12 zeroX6 zeroX6) zer

central : Trit → Heisenberg6
central phase = heisenberg6 (symplectic12 zeroX6 zeroX6) phase

translationGenerator : G.Axis6 → Heisenberg6
translationGenerator i = heisenberg6 (translationBasis i) zer

modulationGenerator : G.Axis6 → Heisenberg6
modulationGenerator i = heisenberg6 (modulationBasis i) zer

------------------------------------------------------------------------
-- 4. The commutator exponent seen by the central extension is exactly the
--    same Kronecker/Weyl exponent already proved at operator level.
------------------------------------------------------------------------

generatorCommutatorExponent : G.Axis6 → G.Axis6 → Trit
generatorCommutatorExponent i j =
  symplecticPair (translationBasis i) (modulationBasis j)

generatorCommutatorMatchesWeyl :
  (i j : G.Axis6) → generatorCommutatorExponent i j ≡ G.kronecker i j
generatorCommutatorMatchesWeyl = translationModulationPair

sameAxisCommutatorIsCentralGenerator :
  (i : G.Axis6) → generatorCommutatorExponent i i ≡ pos
sameAxisCommutatorIsCentralGenerator = canonicalBasisPairIsNontrivial

------------------------------------------------------------------------
-- 5. Boundary: this is now an explicit central-extension *candidate group*
--    with its standard cocycle and basis-nondegeneracy witnesses.  Full group
--    axioms, global quotient nondegeneracy, irreducibility and uniqueness are
--    deliberately separate obligations.
------------------------------------------------------------------------

record HeisenbergCentralExtensionBoundary : Set where
  constructor heisenbergCentralExtensionBoundary
  field
    twelveDimensionalQuotientCarrierConstructed : Bool
    centralPhaseCarrierConstructed : Bool
    heisenbergCocycleCompositionConstructed : Bool
    alternatingCommutatorPairingConstructed : Bool
    sixCanonicalDualPairsNontrivial : Bool
    generatorCommutatorMatchesExistingWeylLaw : Bool
    fullAssociativityProvedHere : Bool
    inverseLawProvedHere : Bool
    globalPairingNondegeneracyProvedHere : Bool
    schrodingerIrreducibilityProvedHere : Bool
    finiteStoneVonNeumannUniquenessProvedHere : Bool
open HeisenbergCentralExtensionBoundary public

canonicalHeisenbergCentralExtensionBoundary : HeisenbergCentralExtensionBoundary
canonicalHeisenbergCentralExtensionBoundary =
  heisenbergCentralExtensionBoundary
    true true true true true true
    false false false false false
