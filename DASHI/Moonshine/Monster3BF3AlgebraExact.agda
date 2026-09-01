module DASHI.Moonshine.Monster3BF3AlgebraExact where

------------------------------------------------------------------------
-- EXACT F_3 ALGEBRA FOR THE MONSTER 3B HEISENBERG MODEL
--
-- These are finite truth-table proofs for the concrete Trit operations already
-- used by the Weyl and central-extension owners.  No abstract field instance
-- is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H

plusAssoc : (a b c : Trit) →
  G._+3_ (G._+3_ a b) c ≡ G._+3_ a (G._+3_ b c)
plusAssoc neg neg neg = refl
plusAssoc neg neg zer = refl
plusAssoc neg neg pos = refl
plusAssoc neg zer neg = refl
plusAssoc neg zer zer = refl
plusAssoc neg zer pos = refl
plusAssoc neg pos neg = refl
plusAssoc neg pos zer = refl
plusAssoc neg pos pos = refl
plusAssoc zer neg neg = refl
plusAssoc zer neg zer = refl
plusAssoc zer neg pos = refl
plusAssoc zer zer neg = refl
plusAssoc zer zer zer = refl
plusAssoc zer zer pos = refl
plusAssoc zer pos neg = refl
plusAssoc zer pos zer = refl
plusAssoc zer pos pos = refl
plusAssoc pos neg neg = refl
plusAssoc pos neg zer = refl
plusAssoc pos neg pos = refl
plusAssoc pos zer neg = refl
plusAssoc pos zer zer = refl
plusAssoc pos zer pos = refl
plusAssoc pos pos neg = refl
plusAssoc pos pos zer = refl
plusAssoc pos pos pos = refl

plusComm : (a b : Trit) → G._+3_ a b ≡ G._+3_ b a
plusComm neg neg = refl
plusComm neg zer = refl
plusComm neg pos = refl
plusComm zer neg = refl
plusComm zer zer = refl
plusComm zer pos = refl
plusComm pos neg = refl
plusComm pos zer = refl
plusComm pos pos = refl

plusRightZero : (a : Trit) → G._+3_ a zer ≡ a
plusRightZero neg = refl
plusRightZero zer = refl
plusRightZero pos = refl

plusInverseLeft : (a : Trit) → G._+3_ (G.negate3 a) a ≡ zer
plusInverseLeft neg = refl
plusInverseLeft zer = refl
plusInverseLeft pos = refl

plusInverseRight : (a : Trit) → G._+3_ a (G.negate3 a) ≡ zer
plusInverseRight neg = refl
plusInverseRight zer = refl
plusInverseRight pos = refl

mulAssoc : (a b c : Trit) → H._*3_ (H._*3_ a b) c ≡ H._*3_ a (H._*3_ b c)
mulAssoc neg neg neg = refl
mulAssoc neg neg zer = refl
mulAssoc neg neg pos = refl
mulAssoc neg zer neg = refl
mulAssoc neg zer zer = refl
mulAssoc neg zer pos = refl
mulAssoc neg pos neg = refl
mulAssoc neg pos zer = refl
mulAssoc neg pos pos = refl
mulAssoc zer neg neg = refl
mulAssoc zer neg zer = refl
mulAssoc zer neg pos = refl
mulAssoc zer zer neg = refl
mulAssoc zer zer zer = refl
mulAssoc zer zer pos = refl
mulAssoc zer pos neg = refl
mulAssoc zer pos zer = refl
mulAssoc zer pos pos = refl
mulAssoc pos neg neg = refl
mulAssoc pos neg zer = refl
mulAssoc pos neg pos = refl
mulAssoc pos zer neg = refl
mulAssoc pos zer zer = refl
mulAssoc pos zer pos = refl
mulAssoc pos pos neg = refl
mulAssoc pos pos zer = refl
mulAssoc pos pos pos = refl

mulComm : (a b : Trit) → H._*3_ a b ≡ H._*3_ b a
mulComm neg neg = refl
mulComm neg zer = refl
mulComm neg pos = refl
mulComm zer neg = refl
mulComm zer zer = refl
mulComm zer pos = refl
mulComm pos neg = refl
mulComm pos zer = refl
mulComm pos pos = refl

leftDistrib : (a b c : Trit) →
  H._*3_ a (G._+3_ b c) ≡ G._+3_ (H._*3_ a b) (H._*3_ a c)
leftDistrib neg neg neg = refl
leftDistrib neg neg zer = refl
leftDistrib neg neg pos = refl
leftDistrib neg zer neg = refl
leftDistrib neg zer zer = refl
leftDistrib neg zer pos = refl
leftDistrib neg pos neg = refl
leftDistrib neg pos zer = refl
leftDistrib neg pos pos = refl
leftDistrib zer neg neg = refl
leftDistrib zer neg zer = refl
leftDistrib zer neg pos = refl
leftDistrib zer zer neg = refl
leftDistrib zer zer zer = refl
leftDistrib zer zer pos = refl
leftDistrib zer pos neg = refl
leftDistrib zer pos zer = refl
leftDistrib zer pos pos = refl
leftDistrib pos neg neg = refl
leftDistrib pos neg zer = refl
leftDistrib pos neg pos = refl
leftDistrib pos zer neg = refl
leftDistrib pos zer zer = refl
leftDistrib pos zer pos = refl
leftDistrib pos pos neg = refl
leftDistrib pos pos zer = refl
leftDistrib pos pos pos = refl

rightDistrib : (a b c : Trit) →
  H._*3_ (G._+3_ a b) c ≡ G._+3_ (H._*3_ a c) (H._*3_ b c)
rightDistrib neg neg neg = refl
rightDistrib neg neg zer = refl
rightDistrib neg neg pos = refl
rightDistrib neg zer neg = refl
rightDistrib neg zer zer = refl
rightDistrib neg zer pos = refl
rightDistrib neg pos neg = refl
rightDistrib neg pos zer = refl
rightDistrib neg pos pos = refl
rightDistrib zer neg neg = refl
rightDistrib zer neg zer = refl
rightDistrib zer neg pos = refl
rightDistrib zer zer neg = refl
rightDistrib zer zer zer = refl
rightDistrib zer zer pos = refl
rightDistrib zer pos neg = refl
rightDistrib zer pos zer = refl
rightDistrib zer pos pos = refl
rightDistrib pos neg neg = refl
rightDistrib pos neg zer = refl
rightDistrib pos neg pos = refl
rightDistrib pos zer neg = refl
rightDistrib pos zer zer = refl
rightDistrib pos zer pos = refl
rightDistrib pos pos neg = refl
rightDistrib pos pos zer = refl
rightDistrib pos pos pos = refl

negateAdd : (a b : Trit) →
  G.negate3 (G._+3_ a b) ≡ G._+3_ (G.negate3 a) (G.negate3 b)
negateAdd neg neg = refl
negateAdd neg zer = refl
negateAdd neg pos = refl
negateAdd zer neg = refl
negateAdd zer zer = refl
negateAdd zer pos = refl
negateAdd pos neg = refl
negateAdd pos zer = refl
negateAdd pos pos = refl

record F3AlgebraBoundary : Set where
  constructor f3AlgebraBoundary
  field
    additiveAssociativity : Bool
    additiveCommutativity : Bool
    additiveInverse : Bool
    multiplicativeAssociativity : Bool
    multiplicativeCommutativity : Bool
    distributivity : Bool
open F3AlgebraBoundary public

canonicalF3AlgebraBoundary : F3AlgebraBoundary
canonicalF3AlgebraBoundary = f3AlgebraBoundary true true true true true true
