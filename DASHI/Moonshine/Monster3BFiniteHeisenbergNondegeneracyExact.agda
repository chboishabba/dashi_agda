module DASHI.Moonshine.Monster3BFiniteHeisenbergNondegeneracyExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE NONDEGENERACY OF THE F_3^12 HEISENBERG QUOTIENT
--
-- Every nonzero quotient vector carries a proof-relevant first nonzero
-- coordinate.  The matching dual basis vector then has nonzero symplectic
-- pairing.  This closes global nondegeneracy without importing linear algebra
-- or enumerating all 3^12 states.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (Σ; _,_; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

------------------------------------------------------------------------
-- 1. Proof-relevant nonzero trits and elementary scalar identities.
------------------------------------------------------------------------

data NonzeroTrit : Trit → Set where
  negNonzero : NonzeroTrit neg
  posNonzero : NonzeroTrit pos

nonzeroNegate : {a : Trit} → NonzeroTrit a → NonzeroTrit (G.negate3 a)
nonzeroNegate negNonzero = posNonzero
nonzeroNegate posNonzero = negNonzero

plusRightZero : (a : Trit) → G._+3_ a zer ≡ a
plusRightZero neg = refl
plusRightZero zer = refl
plusRightZero pos = refl

mulRightZero : (a : Trit) → H._*3_ a zer ≡ zer
mulRightZero neg = refl
mulRightZero zer = refl
mulRightZero pos = refl

mulRightPos : (a : Trit) → H._*3_ a pos ≡ a
mulRightPos neg = refl
mulRightPos zer = refl
mulRightPos pos = refl

------------------------------------------------------------------------
-- 2. Pairing with a standard basis vector reads the selected coordinate.
------------------------------------------------------------------------

dotRightBasis : (x : G.X6) (i : G.Axis6) →
  H.dot6 x (H.basis i) ≡ G.coordinate i x
dotRightBasis (G.x6 a b c d e f) G.axis0
  rewrite mulRightPos a | mulRightZero b | mulRightZero c
        | mulRightZero d | mulRightZero e | mulRightZero f
        | plusRightZero a = refl
dotRightBasis (G.x6 a b c d e f) G.axis1
  rewrite mulRightZero a | mulRightPos b | mulRightZero c
        | mulRightZero d | mulRightZero e | mulRightZero f
        | plusRightZero b = refl
dotRightBasis (G.x6 a b c d e f) G.axis2
  rewrite mulRightZero a | mulRightZero b | mulRightPos c
        | mulRightZero d | mulRightZero e | mulRightZero f
        | plusRightZero c = refl
dotRightBasis (G.x6 a b c d e f) G.axis3
  rewrite mulRightZero a | mulRightZero b | mulRightZero c
        | mulRightPos d | mulRightZero e | mulRightZero f
        | plusRightZero d = refl
dotRightBasis (G.x6 a b c d e f) G.axis4
  rewrite mulRightZero a | mulRightZero b | mulRightZero c
        | mulRightZero d | mulRightPos e | mulRightZero f
        | plusRightZero e = refl
dotRightBasis (G.x6 a b c d e f) G.axis5
  rewrite mulRightZero a | mulRightZero b | mulRightZero c
        | mulRightZero d | mulRightZero e | mulRightPos f
        | plusRightZero f = refl

dotLeftBasis : (i : G.Axis6) (x : G.X6) →
  H.dot6 (H.basis i) x ≡ G.coordinate i x
dotLeftBasis G.axis0 (G.x6 a b c d e f)
  rewrite plusRightZero a = refl
dotLeftBasis G.axis1 (G.x6 a b c d e f)
  rewrite plusRightZero b = refl
dotLeftBasis G.axis2 (G.x6 a b c d e f)
  rewrite plusRightZero c = refl
dotLeftBasis G.axis3 (G.x6 a b c d e f)
  rewrite plusRightZero d = refl
dotLeftBasis G.axis4 (G.x6 a b c d e f)
  rewrite plusRightZero e = refl
dotLeftBasis G.axis5 (G.x6 a b c d e f)
  rewrite plusRightZero f = refl

dotRightZero : (x : G.X6) → H.dot6 x H.zeroX6 ≡ zer
dotRightZero (G.x6 a b c d e f)
  rewrite mulRightZero a | mulRightZero b | mulRightZero c
        | mulRightZero d | mulRightZero e | mulRightZero f = refl

------------------------------------------------------------------------
-- 3. Complete constructive zero/nonzero classification of X6.
------------------------------------------------------------------------

CoordinateWitness : G.X6 → Set
CoordinateWitness x = Σ G.Axis6 (λ i → NonzeroTrit (G.coordinate i x))

classifyX6 : (x : G.X6) → (x ≡ H.zeroX6) ⊎ CoordinateWitness x
classifyX6 (G.x6 neg b c d e f) = inj₂ (G.axis0 , negNonzero)
classifyX6 (G.x6 pos b c d e f) = inj₂ (G.axis0 , posNonzero)
classifyX6 (G.x6 zer neg c d e f) = inj₂ (G.axis1 , negNonzero)
classifyX6 (G.x6 zer pos c d e f) = inj₂ (G.axis1 , posNonzero)
classifyX6 (G.x6 zer zer neg d e f) = inj₂ (G.axis2 , negNonzero)
classifyX6 (G.x6 zer zer pos d e f) = inj₂ (G.axis2 , posNonzero)
classifyX6 (G.x6 zer zer zer neg e f) = inj₂ (G.axis3 , negNonzero)
classifyX6 (G.x6 zer zer zer pos e f) = inj₂ (G.axis3 , posNonzero)
classifyX6 (G.x6 zer zer zer zer neg f) = inj₂ (G.axis4 , negNonzero)
classifyX6 (G.x6 zer zer zer zer pos f) = inj₂ (G.axis4 , posNonzero)
classifyX6 (G.x6 zer zer zer zer zer neg) = inj₂ (G.axis5 , negNonzero)
classifyX6 (G.x6 zer zer zer zer zer pos) = inj₂ (G.axis5 , posNonzero)
classifyX6 (G.x6 zer zer zer zer zer zer) = inj₁ refl

------------------------------------------------------------------------
-- 4. Quotient nonzero witnesses and canonical dual-vector synthesis.
------------------------------------------------------------------------

QuotientZero : H.Symplectic12 → Set
QuotientZero u =
  (H.translationPart u ≡ H.zeroX6) ×
  (H.modulationPart u ≡ H.zeroX6)

data QuotientNonzero (u : H.Symplectic12) : Set where
  translationNonzero : CoordinateWitness (H.translationPart u) → QuotientNonzero u
  modulationNonzero : CoordinateWitness (H.modulationPart u) → QuotientNonzero u

classifyQuotient : (u : H.Symplectic12) → QuotientZero u ⊎ QuotientNonzero u
classifyQuotient (H.symplectic12 x ξ) with classifyX6 x
... | inj₂ witness = inj₂ (translationNonzero witness)
... | inj₁ xZero with classifyX6 ξ
...   | inj₂ witness = inj₂ (modulationNonzero witness)
...   | inj₁ ξZero = inj₁ (xZero , ξZero)

dualWitness : {u : H.Symplectic12} → QuotientNonzero u → H.Symplectic12
dualWitness (translationNonzero (i , nz)) = H.modulationBasis i
dualWitness (modulationNonzero (i , nz)) = H.translationBasis i

pairWithDualIsNonzero :
  {u : H.Symplectic12} →
  (nz : QuotientNonzero u) →
  NonzeroTrit (H.symplecticPair u (dualWitness nz))
pairWithDualIsNonzero {H.symplectic12 x ξ} (translationNonzero (i , nz))
  rewrite dotRightBasis x i | dotRightZero ξ | plusRightZero (G.coordinate i x)
  = nz
pairWithDualIsNonzero {H.symplectic12 x ξ} (modulationNonzero (i , nz))
  rewrite dotRightZero x | dotLeftBasis i ξ
  = nonzeroNegate nz

------------------------------------------------------------------------
-- 5. Global proof-relevant nondegeneracy theorem.
------------------------------------------------------------------------

NondegenerateWitness : H.Symplectic12 → Set
NondegenerateWitness u =
  Σ H.Symplectic12 (λ v → NonzeroTrit (H.symplecticPair u v))

globalNondegeneracy :
  {u : H.Symplectic12} → QuotientNonzero u → NondegenerateWitness u
globalNondegeneracy nz = dualWitness nz , pairWithDualIsNonzero nz

zeroOrNondegenerateWitness :
  (u : H.Symplectic12) → QuotientZero u ⊎ NondegenerateWitness u
zeroOrNondegenerateWitness u with classifyQuotient u
... | inj₁ isZero = inj₁ isZero
... | inj₂ isNonzero = inj₂ (globalNondegeneracy isNonzero)

------------------------------------------------------------------------
-- 6. Boundary.
------------------------------------------------------------------------

record HeisenbergNondegeneracyBoundary : Set where
  constructor heisenbergNondegeneracyBoundary
  field
    everyX6ClassifiedZeroOrCoordinateNonzero : Bool
    everyQuotientClassifiedZeroOrNonzero : Bool
    everyNonzeroQuotientHasExplicitDualWitness : Bool
    globalSymplecticNondegeneracyProved : Bool
    irreducibilityProvedHere : Bool
    stoneVonNeumannUniquenessProvedHere : Bool
open HeisenbergNondegeneracyBoundary public

canonicalHeisenbergNondegeneracyBoundary : HeisenbergNondegeneracyBoundary
canonicalHeisenbergNondegeneracyBoundary =
  heisenbergNondegeneracyBoundary true true true true false false
