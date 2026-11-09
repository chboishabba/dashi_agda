module DASHI.Moonshine.Y443AllCoxeterGraphLawsFrom80Exact where

------------------------------------------------------------------------
-- ACTUAL 80 RELATORS => ALL GRAPH COXETER SOURCE LAWS.
--
-- Each of the 12 square relations and 66 unordered-pair relations is
-- selected by EXACT native index from the existing original word list.
-- The index equality is computed under Agda reduction, not supplied as
-- an external membership certificate. The source consequences owner
-- then derives ALL 12 node squares, 55 nonedge commutations and 11
-- adjacent m=3 braids, both orientations, by finite case analysis.
--
-- Thus the path-shift semantic compiler needs only the ORIGINAL
-- RelatorsSatisfied gi nodes Y.monsterRelators witness and no extra
-- local-Coxeter oracle.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDNonadjacentRelatorConsequencesExact as Rel
import DASHI.Moonshine.Y443CoxeterRelatorSemanticLawsExact as Laws
import DASHI.Moonshine.Y443JMDThreePathFiniteRewriteExact as Finite
import DASHI.Moonshine.Y443Nonary72EquivarianceNoGoExact as Canon
import DASHI.Moonshine.Y443JMDPathShiftSemanticCompilerExact as Path
import DASHI.Moonshine.Y443JMDAllTwelveNodeWordCompilerExact as All
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as Words
import DASHI.Moonshine.Y443VNaturalPairGenerationExact as Pair
import DASHI.Moonshine.TwistedModuleModularity as TM

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

data MaybeWord : Set where
  none : MaybeWord
  some : Y.Word → MaybeWord

nth : Nat → List Y.Word → MaybeWord
nth zero [] = none
nth zero (w ∷ xs) = some w
nth (suc n) [] = none
nth (suc n) (_ ∷ xs) = nth n xs

memberFromNth :
  (word : Y.Word) (n : Nat) (words : List Y.Word) →
  nth n words ≡ some word →
  Rel._∈_ word words
memberFromNth word zero [] ()
memberFromNth word zero (w ∷ xs) refl = Rel.here
memberFromNth word (suc n) [] ()
memberFromNth word (suc n) (w ∷ xs) eq =
  Rel.there (memberFromNth word n xs eq)

squareIndex : Y.Node → Nat
squareIndex Y.a = 0
squareIndex Y.b1 = 1
squareIndex Y.c1 = 2
squareIndex Y.d1 = 3
squareIndex Y.e1 = 4
squareIndex Y.b2 = 5
squareIndex Y.c2 = 6
squareIndex Y.d2 = 7
squareIndex Y.e2 = 8
squareIndex Y.b3 = 9
squareIndex Y.c3 = 10
squareIndex Y.d3 = 11

squareIndexCorrect :
  (n : Y.Node) →
  nth (squareIndex n) Y.monsterRelators ≡ some (Y.square n)
squareIndexCorrect Y.a = refl
squareIndexCorrect Y.b1 = refl
squareIndexCorrect Y.c1 = refl
squareIndexCorrect Y.d1 = refl
squareIndexCorrect Y.e1 = refl
squareIndexCorrect Y.b2 = refl
squareIndexCorrect Y.c2 = refl
squareIndexCorrect Y.d2 = refl
squareIndexCorrect Y.e2 = refl
squareIndexCorrect Y.b3 = refl
squareIndexCorrect Y.c3 = refl
squareIndexCorrect Y.d3 = refl

squareMember :
  (n : Y.Node) → Rel._∈_ (Y.square n) Y.monsterRelators
squareMember n =
  memberFromNth (Y.square n) (squareIndex n)
    Y.monsterRelators (squareIndexCorrect n)

-- Indexing exact original 66 canonical pairs; equal pairs index 0
-- only as a total-function value and are excluded by eqNode=false.
pairIndex : Y.Node → Y.Node → Nat
pairIndex Y.a Y.a = 0
pairIndex Y.a Y.b1 = 12
pairIndex Y.a Y.c1 = 13
pairIndex Y.a Y.d1 = 14
pairIndex Y.a Y.e1 = 15
pairIndex Y.a Y.b2 = 16
pairIndex Y.a Y.c2 = 17
pairIndex Y.a Y.d2 = 18
pairIndex Y.a Y.e2 = 19
pairIndex Y.a Y.b3 = 20
pairIndex Y.a Y.c3 = 21
pairIndex Y.a Y.d3 = 22
pairIndex Y.b1 Y.a = 12
pairIndex Y.b1 Y.b1 = 0
pairIndex Y.b1 Y.c1 = 23
pairIndex Y.b1 Y.d1 = 24
pairIndex Y.b1 Y.e1 = 25
pairIndex Y.b1 Y.b2 = 26
pairIndex Y.b1 Y.c2 = 27
pairIndex Y.b1 Y.d2 = 28
pairIndex Y.b1 Y.e2 = 29
pairIndex Y.b1 Y.b3 = 30
pairIndex Y.b1 Y.c3 = 31
pairIndex Y.b1 Y.d3 = 32
pairIndex Y.c1 Y.a = 13
pairIndex Y.c1 Y.b1 = 23
pairIndex Y.c1 Y.c1 = 0
pairIndex Y.c1 Y.d1 = 33
pairIndex Y.c1 Y.e1 = 34
pairIndex Y.c1 Y.b2 = 35
pairIndex Y.c1 Y.c2 = 36
pairIndex Y.c1 Y.d2 = 37
pairIndex Y.c1 Y.e2 = 38
pairIndex Y.c1 Y.b3 = 39
pairIndex Y.c1 Y.c3 = 40
pairIndex Y.c1 Y.d3 = 41
pairIndex Y.d1 Y.a = 14
pairIndex Y.d1 Y.b1 = 24
pairIndex Y.d1 Y.c1 = 33
pairIndex Y.d1 Y.d1 = 0
pairIndex Y.d1 Y.e1 = 42
pairIndex Y.d1 Y.b2 = 43
pairIndex Y.d1 Y.c2 = 44
pairIndex Y.d1 Y.d2 = 45
pairIndex Y.d1 Y.e2 = 46
pairIndex Y.d1 Y.b3 = 47
pairIndex Y.d1 Y.c3 = 48
pairIndex Y.d1 Y.d3 = 49
pairIndex Y.e1 Y.a = 15
pairIndex Y.e1 Y.b1 = 25
pairIndex Y.e1 Y.c1 = 34
pairIndex Y.e1 Y.d1 = 42
pairIndex Y.e1 Y.e1 = 0
pairIndex Y.e1 Y.b2 = 50
pairIndex Y.e1 Y.c2 = 51
pairIndex Y.e1 Y.d2 = 52
pairIndex Y.e1 Y.e2 = 53
pairIndex Y.e1 Y.b3 = 54
pairIndex Y.e1 Y.c3 = 55
pairIndex Y.e1 Y.d3 = 56
pairIndex Y.b2 Y.a = 16
pairIndex Y.b2 Y.b1 = 26
pairIndex Y.b2 Y.c1 = 35
pairIndex Y.b2 Y.d1 = 43
pairIndex Y.b2 Y.e1 = 50
pairIndex Y.b2 Y.b2 = 0
pairIndex Y.b2 Y.c2 = 57
pairIndex Y.b2 Y.d2 = 58
pairIndex Y.b2 Y.e2 = 59
pairIndex Y.b2 Y.b3 = 60
pairIndex Y.b2 Y.c3 = 61
pairIndex Y.b2 Y.d3 = 62
pairIndex Y.c2 Y.a = 17
pairIndex Y.c2 Y.b1 = 27
pairIndex Y.c2 Y.c1 = 36
pairIndex Y.c2 Y.d1 = 44
pairIndex Y.c2 Y.e1 = 51
pairIndex Y.c2 Y.b2 = 57
pairIndex Y.c2 Y.c2 = 0
pairIndex Y.c2 Y.d2 = 63
pairIndex Y.c2 Y.e2 = 64
pairIndex Y.c2 Y.b3 = 65
pairIndex Y.c2 Y.c3 = 66
pairIndex Y.c2 Y.d3 = 67
pairIndex Y.d2 Y.a = 18
pairIndex Y.d2 Y.b1 = 28
pairIndex Y.d2 Y.c1 = 37
pairIndex Y.d2 Y.d1 = 45
pairIndex Y.d2 Y.e1 = 52
pairIndex Y.d2 Y.b2 = 58
pairIndex Y.d2 Y.c2 = 63
pairIndex Y.d2 Y.d2 = 0
pairIndex Y.d2 Y.e2 = 68
pairIndex Y.d2 Y.b3 = 69
pairIndex Y.d2 Y.c3 = 70
pairIndex Y.d2 Y.d3 = 71
pairIndex Y.e2 Y.a = 19
pairIndex Y.e2 Y.b1 = 29
pairIndex Y.e2 Y.c1 = 38
pairIndex Y.e2 Y.d1 = 46
pairIndex Y.e2 Y.e1 = 53
pairIndex Y.e2 Y.b2 = 59
pairIndex Y.e2 Y.c2 = 64
pairIndex Y.e2 Y.d2 = 68
pairIndex Y.e2 Y.e2 = 0
pairIndex Y.e2 Y.b3 = 72
pairIndex Y.e2 Y.c3 = 73
pairIndex Y.e2 Y.d3 = 74
pairIndex Y.b3 Y.a = 20
pairIndex Y.b3 Y.b1 = 30
pairIndex Y.b3 Y.c1 = 39
pairIndex Y.b3 Y.d1 = 47
pairIndex Y.b3 Y.e1 = 54
pairIndex Y.b3 Y.b2 = 60
pairIndex Y.b3 Y.c2 = 65
pairIndex Y.b3 Y.d2 = 69
pairIndex Y.b3 Y.e2 = 72
pairIndex Y.b3 Y.b3 = 0
pairIndex Y.b3 Y.c3 = 75
pairIndex Y.b3 Y.d3 = 76
pairIndex Y.c3 Y.a = 21
pairIndex Y.c3 Y.b1 = 31
pairIndex Y.c3 Y.c1 = 40
pairIndex Y.c3 Y.d1 = 48
pairIndex Y.c3 Y.e1 = 55
pairIndex Y.c3 Y.b2 = 61
pairIndex Y.c3 Y.c2 = 66
pairIndex Y.c3 Y.d2 = 70
pairIndex Y.c3 Y.e2 = 73
pairIndex Y.c3 Y.b3 = 75
pairIndex Y.c3 Y.c3 = 0
pairIndex Y.c3 Y.d3 = 77
pairIndex Y.d3 Y.a = 22
pairIndex Y.d3 Y.b1 = 32
pairIndex Y.d3 Y.c1 = 41
pairIndex Y.d3 Y.d1 = 49
pairIndex Y.d3 Y.e1 = 56
pairIndex Y.d3 Y.b2 = 62
pairIndex Y.d3 Y.c2 = 67
pairIndex Y.d3 Y.d2 = 71
pairIndex Y.d3 Y.e2 = 74
pairIndex Y.d3 Y.b3 = 76
pairIndex Y.d3 Y.c3 = 77
pairIndex Y.d3 Y.d3 = 0

canonicalPairAtCorrect :
  (x y : Y.Node) → Finite.eqNode x y ≡ false →
  nth (pairIndex x y) Y.monsterRelators
  ≡ some (Y.pairRelator (Canon.canonicalPair x y))
canonicalPairAtCorrect Y.a Y.a ()
canonicalPairAtCorrect Y.a Y.b1 refl = refl
canonicalPairAtCorrect Y.a Y.c1 refl = refl
canonicalPairAtCorrect Y.a Y.d1 refl = refl
canonicalPairAtCorrect Y.a Y.e1 refl = refl
canonicalPairAtCorrect Y.a Y.b2 refl = refl
canonicalPairAtCorrect Y.a Y.c2 refl = refl
canonicalPairAtCorrect Y.a Y.d2 refl = refl
canonicalPairAtCorrect Y.a Y.e2 refl = refl
canonicalPairAtCorrect Y.a Y.b3 refl = refl
canonicalPairAtCorrect Y.a Y.c3 refl = refl
canonicalPairAtCorrect Y.a Y.d3 refl = refl
canonicalPairAtCorrect Y.b1 Y.a refl = refl
canonicalPairAtCorrect Y.b1 Y.b1 ()
canonicalPairAtCorrect Y.b1 Y.c1 refl = refl
canonicalPairAtCorrect Y.b1 Y.d1 refl = refl
canonicalPairAtCorrect Y.b1 Y.e1 refl = refl
canonicalPairAtCorrect Y.b1 Y.b2 refl = refl
canonicalPairAtCorrect Y.b1 Y.c2 refl = refl
canonicalPairAtCorrect Y.b1 Y.d2 refl = refl
canonicalPairAtCorrect Y.b1 Y.e2 refl = refl
canonicalPairAtCorrect Y.b1 Y.b3 refl = refl
canonicalPairAtCorrect Y.b1 Y.c3 refl = refl
canonicalPairAtCorrect Y.b1 Y.d3 refl = refl
canonicalPairAtCorrect Y.c1 Y.a refl = refl
canonicalPairAtCorrect Y.c1 Y.b1 refl = refl
canonicalPairAtCorrect Y.c1 Y.c1 ()
canonicalPairAtCorrect Y.c1 Y.d1 refl = refl
canonicalPairAtCorrect Y.c1 Y.e1 refl = refl
canonicalPairAtCorrect Y.c1 Y.b2 refl = refl
canonicalPairAtCorrect Y.c1 Y.c2 refl = refl
canonicalPairAtCorrect Y.c1 Y.d2 refl = refl
canonicalPairAtCorrect Y.c1 Y.e2 refl = refl
canonicalPairAtCorrect Y.c1 Y.b3 refl = refl
canonicalPairAtCorrect Y.c1 Y.c3 refl = refl
canonicalPairAtCorrect Y.c1 Y.d3 refl = refl
canonicalPairAtCorrect Y.d1 Y.a refl = refl
canonicalPairAtCorrect Y.d1 Y.b1 refl = refl
canonicalPairAtCorrect Y.d1 Y.c1 refl = refl
canonicalPairAtCorrect Y.d1 Y.d1 ()
canonicalPairAtCorrect Y.d1 Y.e1 refl = refl
canonicalPairAtCorrect Y.d1 Y.b2 refl = refl
canonicalPairAtCorrect Y.d1 Y.c2 refl = refl
canonicalPairAtCorrect Y.d1 Y.d2 refl = refl
canonicalPairAtCorrect Y.d1 Y.e2 refl = refl
canonicalPairAtCorrect Y.d1 Y.b3 refl = refl
canonicalPairAtCorrect Y.d1 Y.c3 refl = refl
canonicalPairAtCorrect Y.d1 Y.d3 refl = refl
canonicalPairAtCorrect Y.e1 Y.a refl = refl
canonicalPairAtCorrect Y.e1 Y.b1 refl = refl
canonicalPairAtCorrect Y.e1 Y.c1 refl = refl
canonicalPairAtCorrect Y.e1 Y.d1 refl = refl
canonicalPairAtCorrect Y.e1 Y.e1 ()
canonicalPairAtCorrect Y.e1 Y.b2 refl = refl
canonicalPairAtCorrect Y.e1 Y.c2 refl = refl
canonicalPairAtCorrect Y.e1 Y.d2 refl = refl
canonicalPairAtCorrect Y.e1 Y.e2 refl = refl
canonicalPairAtCorrect Y.e1 Y.b3 refl = refl
canonicalPairAtCorrect Y.e1 Y.c3 refl = refl
canonicalPairAtCorrect Y.e1 Y.d3 refl = refl
canonicalPairAtCorrect Y.b2 Y.a refl = refl
canonicalPairAtCorrect Y.b2 Y.b1 refl = refl
canonicalPairAtCorrect Y.b2 Y.c1 refl = refl
canonicalPairAtCorrect Y.b2 Y.d1 refl = refl
canonicalPairAtCorrect Y.b2 Y.e1 refl = refl
canonicalPairAtCorrect Y.b2 Y.b2 ()
canonicalPairAtCorrect Y.b2 Y.c2 refl = refl
canonicalPairAtCorrect Y.b2 Y.d2 refl = refl
canonicalPairAtCorrect Y.b2 Y.e2 refl = refl
canonicalPairAtCorrect Y.b2 Y.b3 refl = refl
canonicalPairAtCorrect Y.b2 Y.c3 refl = refl
canonicalPairAtCorrect Y.b2 Y.d3 refl = refl
canonicalPairAtCorrect Y.c2 Y.a refl = refl
canonicalPairAtCorrect Y.c2 Y.b1 refl = refl
canonicalPairAtCorrect Y.c2 Y.c1 refl = refl
canonicalPairAtCorrect Y.c2 Y.d1 refl = refl
canonicalPairAtCorrect Y.c2 Y.e1 refl = refl
canonicalPairAtCorrect Y.c2 Y.b2 refl = refl
canonicalPairAtCorrect Y.c2 Y.c2 ()
canonicalPairAtCorrect Y.c2 Y.d2 refl = refl
canonicalPairAtCorrect Y.c2 Y.e2 refl = refl
canonicalPairAtCorrect Y.c2 Y.b3 refl = refl
canonicalPairAtCorrect Y.c2 Y.c3 refl = refl
canonicalPairAtCorrect Y.c2 Y.d3 refl = refl
canonicalPairAtCorrect Y.d2 Y.a refl = refl
canonicalPairAtCorrect Y.d2 Y.b1 refl = refl
canonicalPairAtCorrect Y.d2 Y.c1 refl = refl
canonicalPairAtCorrect Y.d2 Y.d1 refl = refl
canonicalPairAtCorrect Y.d2 Y.e1 refl = refl
canonicalPairAtCorrect Y.d2 Y.b2 refl = refl
canonicalPairAtCorrect Y.d2 Y.c2 refl = refl
canonicalPairAtCorrect Y.d2 Y.d2 ()
canonicalPairAtCorrect Y.d2 Y.e2 refl = refl
canonicalPairAtCorrect Y.d2 Y.b3 refl = refl
canonicalPairAtCorrect Y.d2 Y.c3 refl = refl
canonicalPairAtCorrect Y.d2 Y.d3 refl = refl
canonicalPairAtCorrect Y.e2 Y.a refl = refl
canonicalPairAtCorrect Y.e2 Y.b1 refl = refl
canonicalPairAtCorrect Y.e2 Y.c1 refl = refl
canonicalPairAtCorrect Y.e2 Y.d1 refl = refl
canonicalPairAtCorrect Y.e2 Y.e1 refl = refl
canonicalPairAtCorrect Y.e2 Y.b2 refl = refl
canonicalPairAtCorrect Y.e2 Y.c2 refl = refl
canonicalPairAtCorrect Y.e2 Y.d2 refl = refl
canonicalPairAtCorrect Y.e2 Y.e2 ()
canonicalPairAtCorrect Y.e2 Y.b3 refl = refl
canonicalPairAtCorrect Y.e2 Y.c3 refl = refl
canonicalPairAtCorrect Y.e2 Y.d3 refl = refl
canonicalPairAtCorrect Y.b3 Y.a refl = refl
canonicalPairAtCorrect Y.b3 Y.b1 refl = refl
canonicalPairAtCorrect Y.b3 Y.c1 refl = refl
canonicalPairAtCorrect Y.b3 Y.d1 refl = refl
canonicalPairAtCorrect Y.b3 Y.e1 refl = refl
canonicalPairAtCorrect Y.b3 Y.b2 refl = refl
canonicalPairAtCorrect Y.b3 Y.c2 refl = refl
canonicalPairAtCorrect Y.b3 Y.d2 refl = refl
canonicalPairAtCorrect Y.b3 Y.e2 refl = refl
canonicalPairAtCorrect Y.b3 Y.b3 ()
canonicalPairAtCorrect Y.b3 Y.c3 refl = refl
canonicalPairAtCorrect Y.b3 Y.d3 refl = refl
canonicalPairAtCorrect Y.c3 Y.a refl = refl
canonicalPairAtCorrect Y.c3 Y.b1 refl = refl
canonicalPairAtCorrect Y.c3 Y.c1 refl = refl
canonicalPairAtCorrect Y.c3 Y.d1 refl = refl
canonicalPairAtCorrect Y.c3 Y.e1 refl = refl
canonicalPairAtCorrect Y.c3 Y.b2 refl = refl
canonicalPairAtCorrect Y.c3 Y.c2 refl = refl
canonicalPairAtCorrect Y.c3 Y.d2 refl = refl
canonicalPairAtCorrect Y.c3 Y.e2 refl = refl
canonicalPairAtCorrect Y.c3 Y.b3 refl = refl
canonicalPairAtCorrect Y.c3 Y.c3 ()
canonicalPairAtCorrect Y.c3 Y.d3 refl = refl
canonicalPairAtCorrect Y.d3 Y.a refl = refl
canonicalPairAtCorrect Y.d3 Y.b1 refl = refl
canonicalPairAtCorrect Y.d3 Y.c1 refl = refl
canonicalPairAtCorrect Y.d3 Y.d1 refl = refl
canonicalPairAtCorrect Y.d3 Y.e1 refl = refl
canonicalPairAtCorrect Y.d3 Y.b2 refl = refl
canonicalPairAtCorrect Y.d3 Y.c2 refl = refl
canonicalPairAtCorrect Y.d3 Y.d2 refl = refl
canonicalPairAtCorrect Y.d3 Y.e2 refl = refl
canonicalPairAtCorrect Y.d3 Y.b3 refl = refl
canonicalPairAtCorrect Y.d3 Y.c3 refl = refl
canonicalPairAtCorrect Y.d3 Y.d3 ()

pairMember :
  (x y : Y.Node) → Finite.eqNode x y ≡ false →
  Rel._∈_
    (Y.pairRelator (Canon.canonicalPair x y)) Y.monsterRelators
pairMember x y different =
  memberFromNth
    (Y.pairRelator (Canon.canonicalPair x y))
    (pairIndex x y) Y.monsterRelators
    (canonicalPairAtCorrect x y different)

eqNodeSound :
  (x y : Y.Node) → Finite.eqNode x y ≡ true → x ≡ y
eqNodeSound Y.a Y.a refl = refl
eqNodeSound Y.a Y.b1 ()
eqNodeSound Y.a Y.c1 ()
eqNodeSound Y.a Y.d1 ()
eqNodeSound Y.a Y.e1 ()
eqNodeSound Y.a Y.b2 ()
eqNodeSound Y.a Y.c2 ()
eqNodeSound Y.a Y.d2 ()
eqNodeSound Y.a Y.e2 ()
eqNodeSound Y.a Y.b3 ()
eqNodeSound Y.a Y.c3 ()
eqNodeSound Y.a Y.d3 ()
eqNodeSound Y.b1 Y.a ()
eqNodeSound Y.b1 Y.b1 refl = refl
eqNodeSound Y.b1 Y.c1 ()
eqNodeSound Y.b1 Y.d1 ()
eqNodeSound Y.b1 Y.e1 ()
eqNodeSound Y.b1 Y.b2 ()
eqNodeSound Y.b1 Y.c2 ()
eqNodeSound Y.b1 Y.d2 ()
eqNodeSound Y.b1 Y.e2 ()
eqNodeSound Y.b1 Y.b3 ()
eqNodeSound Y.b1 Y.c3 ()
eqNodeSound Y.b1 Y.d3 ()
eqNodeSound Y.c1 Y.a ()
eqNodeSound Y.c1 Y.b1 ()
eqNodeSound Y.c1 Y.c1 refl = refl
eqNodeSound Y.c1 Y.d1 ()
eqNodeSound Y.c1 Y.e1 ()
eqNodeSound Y.c1 Y.b2 ()
eqNodeSound Y.c1 Y.c2 ()
eqNodeSound Y.c1 Y.d2 ()
eqNodeSound Y.c1 Y.e2 ()
eqNodeSound Y.c1 Y.b3 ()
eqNodeSound Y.c1 Y.c3 ()
eqNodeSound Y.c1 Y.d3 ()
eqNodeSound Y.d1 Y.a ()
eqNodeSound Y.d1 Y.b1 ()
eqNodeSound Y.d1 Y.c1 ()
eqNodeSound Y.d1 Y.d1 refl = refl
eqNodeSound Y.d1 Y.e1 ()
eqNodeSound Y.d1 Y.b2 ()
eqNodeSound Y.d1 Y.c2 ()
eqNodeSound Y.d1 Y.d2 ()
eqNodeSound Y.d1 Y.e2 ()
eqNodeSound Y.d1 Y.b3 ()
eqNodeSound Y.d1 Y.c3 ()
eqNodeSound Y.d1 Y.d3 ()
eqNodeSound Y.e1 Y.a ()
eqNodeSound Y.e1 Y.b1 ()
eqNodeSound Y.e1 Y.c1 ()
eqNodeSound Y.e1 Y.d1 ()
eqNodeSound Y.e1 Y.e1 refl = refl
eqNodeSound Y.e1 Y.b2 ()
eqNodeSound Y.e1 Y.c2 ()
eqNodeSound Y.e1 Y.d2 ()
eqNodeSound Y.e1 Y.e2 ()
eqNodeSound Y.e1 Y.b3 ()
eqNodeSound Y.e1 Y.c3 ()
eqNodeSound Y.e1 Y.d3 ()
eqNodeSound Y.b2 Y.a ()
eqNodeSound Y.b2 Y.b1 ()
eqNodeSound Y.b2 Y.c1 ()
eqNodeSound Y.b2 Y.d1 ()
eqNodeSound Y.b2 Y.e1 ()
eqNodeSound Y.b2 Y.b2 refl = refl
eqNodeSound Y.b2 Y.c2 ()
eqNodeSound Y.b2 Y.d2 ()
eqNodeSound Y.b2 Y.e2 ()
eqNodeSound Y.b2 Y.b3 ()
eqNodeSound Y.b2 Y.c3 ()
eqNodeSound Y.b2 Y.d3 ()
eqNodeSound Y.c2 Y.a ()
eqNodeSound Y.c2 Y.b1 ()
eqNodeSound Y.c2 Y.c1 ()
eqNodeSound Y.c2 Y.d1 ()
eqNodeSound Y.c2 Y.e1 ()
eqNodeSound Y.c2 Y.b2 ()
eqNodeSound Y.c2 Y.c2 refl = refl
eqNodeSound Y.c2 Y.d2 ()
eqNodeSound Y.c2 Y.e2 ()
eqNodeSound Y.c2 Y.b3 ()
eqNodeSound Y.c2 Y.c3 ()
eqNodeSound Y.c2 Y.d3 ()
eqNodeSound Y.d2 Y.a ()
eqNodeSound Y.d2 Y.b1 ()
eqNodeSound Y.d2 Y.c1 ()
eqNodeSound Y.d2 Y.d1 ()
eqNodeSound Y.d2 Y.e1 ()
eqNodeSound Y.d2 Y.b2 ()
eqNodeSound Y.d2 Y.c2 ()
eqNodeSound Y.d2 Y.d2 refl = refl
eqNodeSound Y.d2 Y.e2 ()
eqNodeSound Y.d2 Y.b3 ()
eqNodeSound Y.d2 Y.c3 ()
eqNodeSound Y.d2 Y.d3 ()
eqNodeSound Y.e2 Y.a ()
eqNodeSound Y.e2 Y.b1 ()
eqNodeSound Y.e2 Y.c1 ()
eqNodeSound Y.e2 Y.d1 ()
eqNodeSound Y.e2 Y.e1 ()
eqNodeSound Y.e2 Y.b2 ()
eqNodeSound Y.e2 Y.c2 ()
eqNodeSound Y.e2 Y.d2 ()
eqNodeSound Y.e2 Y.e2 refl = refl
eqNodeSound Y.e2 Y.b3 ()
eqNodeSound Y.e2 Y.c3 ()
eqNodeSound Y.e2 Y.d3 ()
eqNodeSound Y.b3 Y.a ()
eqNodeSound Y.b3 Y.b1 ()
eqNodeSound Y.b3 Y.c1 ()
eqNodeSound Y.b3 Y.d1 ()
eqNodeSound Y.b3 Y.e1 ()
eqNodeSound Y.b3 Y.b2 ()
eqNodeSound Y.b3 Y.c2 ()
eqNodeSound Y.b3 Y.d2 ()
eqNodeSound Y.b3 Y.e2 ()
eqNodeSound Y.b3 Y.b3 refl = refl
eqNodeSound Y.b3 Y.c3 ()
eqNodeSound Y.b3 Y.d3 ()
eqNodeSound Y.c3 Y.a ()
eqNodeSound Y.c3 Y.b1 ()
eqNodeSound Y.c3 Y.c1 ()
eqNodeSound Y.c3 Y.d1 ()
eqNodeSound Y.c3 Y.e1 ()
eqNodeSound Y.c3 Y.b2 ()
eqNodeSound Y.c3 Y.c2 ()
eqNodeSound Y.c3 Y.d2 ()
eqNodeSound Y.c3 Y.e2 ()
eqNodeSound Y.c3 Y.b3 ()
eqNodeSound Y.c3 Y.c3 refl = refl
eqNodeSound Y.c3 Y.d3 ()
eqNodeSound Y.d3 Y.a ()
eqNodeSound Y.d3 Y.b1 ()
eqNodeSound Y.d3 Y.c1 ()
eqNodeSound Y.d3 Y.d1 ()
eqNodeSound Y.d3 Y.e1 ()
eqNodeSound Y.d3 Y.b2 ()
eqNodeSound Y.d3 Y.c2 ()
eqNodeSound Y.d3 Y.d2 ()
eqNodeSound Y.d3 Y.e2 ()
eqNodeSound Y.d3 Y.b3 ()
eqNodeSound Y.d3 Y.c3 ()
eqNodeSound Y.d3 Y.d3 refl = refl

andLeftTrue : (x y : Bool) → Finite.andB x y ≡ true → x ≡ true
andLeftTrue true true refl = refl
andLeftTrue true false ()
andLeftTrue false true ()
andLeftTrue false false ()

andRightTrue : (x y : Bool) → Finite.andB x y ≡ true → y ≡ true
andRightTrue true true refl = refl
andRightTrue true false ()
andRightTrue false true ()
andRightTrue false false ()

module Source
  {G : Set} (gi : TM.GroupWithInverse G)
  (nodes : Y.Node → G)
  (all : Pair.RelatorsSatisfied gi nodes Y.monsterRelators) where

  module R = Rel.SourceConsequences gi nodes all
  module L = Laws.Laws gi nodes all

  squareOriginal :
    (n : Y.Node) →
    Pair.multiply gi (nodes n) (nodes n) ≡ Pair.identity gi
  squareOriginal n = R.squareFrom n (squareMember n)

  commuteFromSource :
    (x y : Y.Node) →
    Finite.canCommute x y ≡ true →
    Pair.multiply gi (nodes x) (nodes y)
    ≡ Pair.multiply gi (nodes y) (nodes x)
  commuteFromSource Y.a Y.a ()
commuteFromSource Y.a Y.b1 ()
commuteFromSource Y.a Y.c1 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c1)
      (squareOriginal Y.a) (squareOriginal Y.c1)
      (R.nonedgeProductSquare Y.a Y.c1
        (pairMember Y.a Y.c1 refl) refl)
commuteFromSource Y.a Y.d1 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d1)
      (squareOriginal Y.a) (squareOriginal Y.d1)
      (R.nonedgeProductSquare Y.a Y.d1
        (pairMember Y.a Y.d1 refl) refl)
commuteFromSource Y.a Y.e1 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.e1)
      (squareOriginal Y.a) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.a Y.e1
        (pairMember Y.a Y.e1 refl) refl)
commuteFromSource Y.a Y.b2 ()
commuteFromSource Y.a Y.c2 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c2)
      (squareOriginal Y.a) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.a Y.c2
        (pairMember Y.a Y.c2 refl) refl)
commuteFromSource Y.a Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d2)
      (squareOriginal Y.a) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.a Y.d2
        (pairMember Y.a Y.d2 refl) refl)
commuteFromSource Y.a Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.e2)
      (squareOriginal Y.a) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.a Y.e2
        (pairMember Y.a Y.e2 refl) refl)
commuteFromSource Y.a Y.b3 ()
commuteFromSource Y.a Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c3)
      (squareOriginal Y.a) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.a Y.c3
        (pairMember Y.a Y.c3 refl) refl)
commuteFromSource Y.a Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d3)
      (squareOriginal Y.a) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.a Y.d3
        (pairMember Y.a Y.d3 refl) refl)
commuteFromSource Y.b1 Y.a ()
commuteFromSource Y.b1 Y.b1 ()
commuteFromSource Y.b1 Y.c1 ()
commuteFromSource Y.b1 Y.d1 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d1)
      (squareOriginal Y.b1) (squareOriginal Y.d1)
      (R.nonedgeProductSquare Y.b1 Y.d1
        (pairMember Y.b1 Y.d1 refl) refl)
commuteFromSource Y.b1 Y.e1 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.e1)
      (squareOriginal Y.b1) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.b1 Y.e1
        (pairMember Y.b1 Y.e1 refl) refl)
commuteFromSource Y.b1 Y.b2 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.b2)
      (squareOriginal Y.b1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.b1 Y.b2
        (pairMember Y.b1 Y.b2 refl) refl)
commuteFromSource Y.b1 Y.c2 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.c2)
      (squareOriginal Y.b1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.b1 Y.c2
        (pairMember Y.b1 Y.c2 refl) refl)
commuteFromSource Y.b1 Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d2)
      (squareOriginal Y.b1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.b1 Y.d2
        (pairMember Y.b1 Y.d2 refl) refl)
commuteFromSource Y.b1 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.e2)
      (squareOriginal Y.b1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.b1 Y.e2
        (pairMember Y.b1 Y.e2 refl) refl)
commuteFromSource Y.b1 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.b3)
      (squareOriginal Y.b1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.b1 Y.b3
        (pairMember Y.b1 Y.b3 refl) refl)
commuteFromSource Y.b1 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.c3)
      (squareOriginal Y.b1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.b1 Y.c3
        (pairMember Y.b1 Y.c3 refl) refl)
commuteFromSource Y.b1 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d3)
      (squareOriginal Y.b1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b1 Y.d3
        (pairMember Y.b1 Y.d3 refl) refl)
commuteFromSource Y.c1 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c1)
      (squareOriginal Y.a) (squareOriginal Y.c1)
      (R.nonedgeProductSquare Y.a Y.c1
        (pairMember Y.a Y.c1 refl) refl))
commuteFromSource Y.c1 Y.b1 ()
commuteFromSource Y.c1 Y.c1 ()
commuteFromSource Y.c1 Y.d1 ()
commuteFromSource Y.c1 Y.e1 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.e1)
      (squareOriginal Y.c1) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.c1 Y.e1
        (pairMember Y.c1 Y.e1 refl) refl)
commuteFromSource Y.c1 Y.b2 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.b2)
      (squareOriginal Y.c1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.c1 Y.b2
        (pairMember Y.c1 Y.b2 refl) refl)
commuteFromSource Y.c1 Y.c2 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.c2)
      (squareOriginal Y.c1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.c1 Y.c2
        (pairMember Y.c1 Y.c2 refl) refl)
commuteFromSource Y.c1 Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.d2)
      (squareOriginal Y.c1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.c1 Y.d2
        (pairMember Y.c1 Y.d2 refl) refl)
commuteFromSource Y.c1 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.e2)
      (squareOriginal Y.c1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.c1 Y.e2
        (pairMember Y.c1 Y.e2 refl) refl)
commuteFromSource Y.c1 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.b3)
      (squareOriginal Y.c1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.c1 Y.b3
        (pairMember Y.c1 Y.b3 refl) refl)
commuteFromSource Y.c1 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.c3)
      (squareOriginal Y.c1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.c1 Y.c3
        (pairMember Y.c1 Y.c3 refl) refl)
commuteFromSource Y.c1 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.d3)
      (squareOriginal Y.c1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.c1 Y.d3
        (pairMember Y.c1 Y.d3 refl) refl)
commuteFromSource Y.d1 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d1)
      (squareOriginal Y.a) (squareOriginal Y.d1)
      (R.nonedgeProductSquare Y.a Y.d1
        (pairMember Y.a Y.d1 refl) refl))
commuteFromSource Y.d1 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d1)
      (squareOriginal Y.b1) (squareOriginal Y.d1)
      (R.nonedgeProductSquare Y.b1 Y.d1
        (pairMember Y.b1 Y.d1 refl) refl))
commuteFromSource Y.d1 Y.c1 ()
commuteFromSource Y.d1 Y.d1 ()
commuteFromSource Y.d1 Y.e1 ()
commuteFromSource Y.d1 Y.b2 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.b2)
      (squareOriginal Y.d1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.d1 Y.b2
        (pairMember Y.d1 Y.b2 refl) refl)
commuteFromSource Y.d1 Y.c2 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.c2)
      (squareOriginal Y.d1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.d1 Y.c2
        (pairMember Y.d1 Y.c2 refl) refl)
commuteFromSource Y.d1 Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.d2)
      (squareOriginal Y.d1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.d1 Y.d2
        (pairMember Y.d1 Y.d2 refl) refl)
commuteFromSource Y.d1 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.e2)
      (squareOriginal Y.d1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.d1 Y.e2
        (pairMember Y.d1 Y.e2 refl) refl)
commuteFromSource Y.d1 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.b3)
      (squareOriginal Y.d1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.d1 Y.b3
        (pairMember Y.d1 Y.b3 refl) refl)
commuteFromSource Y.d1 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.c3)
      (squareOriginal Y.d1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.d1 Y.c3
        (pairMember Y.d1 Y.c3 refl) refl)
commuteFromSource Y.d1 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.d3)
      (squareOriginal Y.d1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.d1 Y.d3
        (pairMember Y.d1 Y.d3 refl) refl)
commuteFromSource Y.e1 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.e1)
      (squareOriginal Y.a) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.a Y.e1
        (pairMember Y.a Y.e1 refl) refl))
commuteFromSource Y.e1 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.e1)
      (squareOriginal Y.b1) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.b1 Y.e1
        (pairMember Y.b1 Y.e1 refl) refl))
commuteFromSource Y.e1 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.e1)
      (squareOriginal Y.c1) (squareOriginal Y.e1)
      (R.nonedgeProductSquare Y.c1 Y.e1
        (pairMember Y.c1 Y.e1 refl) refl))
commuteFromSource Y.e1 Y.d1 ()
commuteFromSource Y.e1 Y.e1 ()
commuteFromSource Y.e1 Y.b2 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.b2)
      (squareOriginal Y.e1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.e1 Y.b2
        (pairMember Y.e1 Y.b2 refl) refl)
commuteFromSource Y.e1 Y.c2 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.c2)
      (squareOriginal Y.e1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.e1 Y.c2
        (pairMember Y.e1 Y.c2 refl) refl)
commuteFromSource Y.e1 Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.d2)
      (squareOriginal Y.e1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.e1 Y.d2
        (pairMember Y.e1 Y.d2 refl) refl)
commuteFromSource Y.e1 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.e2)
      (squareOriginal Y.e1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.e1 Y.e2
        (pairMember Y.e1 Y.e2 refl) refl)
commuteFromSource Y.e1 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.b3)
      (squareOriginal Y.e1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.e1 Y.b3
        (pairMember Y.e1 Y.b3 refl) refl)
commuteFromSource Y.e1 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.c3)
      (squareOriginal Y.e1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.e1 Y.c3
        (pairMember Y.e1 Y.c3 refl) refl)
commuteFromSource Y.e1 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.d3)
      (squareOriginal Y.e1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.e1 Y.d3
        (pairMember Y.e1 Y.d3 refl) refl)
commuteFromSource Y.b2 Y.a ()
commuteFromSource Y.b2 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.b2)
      (squareOriginal Y.b1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.b1 Y.b2
        (pairMember Y.b1 Y.b2 refl) refl))
commuteFromSource Y.b2 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.b2)
      (squareOriginal Y.c1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.c1 Y.b2
        (pairMember Y.c1 Y.b2 refl) refl))
commuteFromSource Y.b2 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.b2)
      (squareOriginal Y.d1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.d1 Y.b2
        (pairMember Y.d1 Y.b2 refl) refl))
commuteFromSource Y.b2 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.b2)
      (squareOriginal Y.e1) (squareOriginal Y.b2)
      (R.nonedgeProductSquare Y.e1 Y.b2
        (pairMember Y.e1 Y.b2 refl) refl))
commuteFromSource Y.b2 Y.b2 ()
commuteFromSource Y.b2 Y.c2 ()
commuteFromSource Y.b2 Y.d2 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d2)
      (squareOriginal Y.b2) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.b2 Y.d2
        (pairMember Y.b2 Y.d2 refl) refl)
commuteFromSource Y.b2 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.e2)
      (squareOriginal Y.b2) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.b2 Y.e2
        (pairMember Y.b2 Y.e2 refl) refl)
commuteFromSource Y.b2 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.b3)
      (squareOriginal Y.b2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.b2 Y.b3
        (pairMember Y.b2 Y.b3 refl) refl)
commuteFromSource Y.b2 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.c3)
      (squareOriginal Y.b2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.b2 Y.c3
        (pairMember Y.b2 Y.c3 refl) refl)
commuteFromSource Y.b2 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d3)
      (squareOriginal Y.b2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b2 Y.d3
        (pairMember Y.b2 Y.d3 refl) refl)
commuteFromSource Y.c2 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c2)
      (squareOriginal Y.a) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.a Y.c2
        (pairMember Y.a Y.c2 refl) refl))
commuteFromSource Y.c2 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.c2)
      (squareOriginal Y.b1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.b1 Y.c2
        (pairMember Y.b1 Y.c2 refl) refl))
commuteFromSource Y.c2 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.c2)
      (squareOriginal Y.c1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.c1 Y.c2
        (pairMember Y.c1 Y.c2 refl) refl))
commuteFromSource Y.c2 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.c2)
      (squareOriginal Y.d1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.d1 Y.c2
        (pairMember Y.d1 Y.c2 refl) refl))
commuteFromSource Y.c2 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.c2)
      (squareOriginal Y.e1) (squareOriginal Y.c2)
      (R.nonedgeProductSquare Y.e1 Y.c2
        (pairMember Y.e1 Y.c2 refl) refl))
commuteFromSource Y.c2 Y.b2 ()
commuteFromSource Y.c2 Y.c2 ()
commuteFromSource Y.c2 Y.d2 ()
commuteFromSource Y.c2 Y.e2 proof =
    R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.e2)
      (squareOriginal Y.c2) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.c2 Y.e2
        (pairMember Y.c2 Y.e2 refl) refl)
commuteFromSource Y.c2 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.b3)
      (squareOriginal Y.c2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.c2 Y.b3
        (pairMember Y.c2 Y.b3 refl) refl)
commuteFromSource Y.c2 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.c3)
      (squareOriginal Y.c2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.c2 Y.c3
        (pairMember Y.c2 Y.c3 refl) refl)
commuteFromSource Y.c2 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.d3)
      (squareOriginal Y.c2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.c2 Y.d3
        (pairMember Y.c2 Y.d3 refl) refl)
commuteFromSource Y.d2 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d2)
      (squareOriginal Y.a) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.a Y.d2
        (pairMember Y.a Y.d2 refl) refl))
commuteFromSource Y.d2 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d2)
      (squareOriginal Y.b1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.b1 Y.d2
        (pairMember Y.b1 Y.d2 refl) refl))
commuteFromSource Y.d2 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.d2)
      (squareOriginal Y.c1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.c1 Y.d2
        (pairMember Y.c1 Y.d2 refl) refl))
commuteFromSource Y.d2 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.d2)
      (squareOriginal Y.d1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.d1 Y.d2
        (pairMember Y.d1 Y.d2 refl) refl))
commuteFromSource Y.d2 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.d2)
      (squareOriginal Y.e1) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.e1 Y.d2
        (pairMember Y.e1 Y.d2 refl) refl))
commuteFromSource Y.d2 Y.b2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d2)
      (squareOriginal Y.b2) (squareOriginal Y.d2)
      (R.nonedgeProductSquare Y.b2 Y.d2
        (pairMember Y.b2 Y.d2 refl) refl))
commuteFromSource Y.d2 Y.c2 ()
commuteFromSource Y.d2 Y.d2 ()
commuteFromSource Y.d2 Y.e2 ()
commuteFromSource Y.d2 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.b3)
      (squareOriginal Y.d2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.d2 Y.b3
        (pairMember Y.d2 Y.b3 refl) refl)
commuteFromSource Y.d2 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.c3)
      (squareOriginal Y.d2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.d2 Y.c3
        (pairMember Y.d2 Y.c3 refl) refl)
commuteFromSource Y.d2 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.d3)
      (squareOriginal Y.d2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.d2 Y.d3
        (pairMember Y.d2 Y.d3 refl) refl)
commuteFromSource Y.e2 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.e2)
      (squareOriginal Y.a) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.a Y.e2
        (pairMember Y.a Y.e2 refl) refl))
commuteFromSource Y.e2 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.e2)
      (squareOriginal Y.b1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.b1 Y.e2
        (pairMember Y.b1 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.e2)
      (squareOriginal Y.c1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.c1 Y.e2
        (pairMember Y.c1 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.e2)
      (squareOriginal Y.d1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.d1 Y.e2
        (pairMember Y.d1 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.e2)
      (squareOriginal Y.e1) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.e1 Y.e2
        (pairMember Y.e1 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.b2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.e2)
      (squareOriginal Y.b2) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.b2 Y.e2
        (pairMember Y.b2 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.c2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.e2)
      (squareOriginal Y.c2) (squareOriginal Y.e2)
      (R.nonedgeProductSquare Y.c2 Y.e2
        (pairMember Y.c2 Y.e2 refl) refl))
commuteFromSource Y.e2 Y.d2 ()
commuteFromSource Y.e2 Y.e2 ()
commuteFromSource Y.e2 Y.b3 proof =
    R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.b3)
      (squareOriginal Y.e2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.e2 Y.b3
        (pairMember Y.e2 Y.b3 refl) refl)
commuteFromSource Y.e2 Y.c3 proof =
    R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.c3)
      (squareOriginal Y.e2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.e2 Y.c3
        (pairMember Y.e2 Y.c3 refl) refl)
commuteFromSource Y.e2 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.d3)
      (squareOriginal Y.e2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.e2 Y.d3
        (pairMember Y.e2 Y.d3 refl) refl)
commuteFromSource Y.b3 Y.a ()
commuteFromSource Y.b3 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.b3)
      (squareOriginal Y.b1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.b1 Y.b3
        (pairMember Y.b1 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.b3)
      (squareOriginal Y.c1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.c1 Y.b3
        (pairMember Y.c1 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.b3)
      (squareOriginal Y.d1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.d1 Y.b3
        (pairMember Y.d1 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.b3)
      (squareOriginal Y.e1) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.e1 Y.b3
        (pairMember Y.e1 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.b2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.b3)
      (squareOriginal Y.b2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.b2 Y.b3
        (pairMember Y.b2 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.c2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.b3)
      (squareOriginal Y.c2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.c2 Y.b3
        (pairMember Y.c2 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.d2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.b3)
      (squareOriginal Y.d2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.d2 Y.b3
        (pairMember Y.d2 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.e2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.b3)
      (squareOriginal Y.e2) (squareOriginal Y.b3)
      (R.nonedgeProductSquare Y.e2 Y.b3
        (pairMember Y.e2 Y.b3 refl) refl))
commuteFromSource Y.b3 Y.b3 ()
commuteFromSource Y.b3 Y.c3 ()
commuteFromSource Y.b3 Y.d3 proof =
    R.commuteFromThreeSquares (nodes Y.b3) (nodes Y.d3)
      (squareOriginal Y.b3) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b3 Y.d3
        (pairMember Y.b3 Y.d3 refl) refl)
commuteFromSource Y.c3 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.c3)
      (squareOriginal Y.a) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.a Y.c3
        (pairMember Y.a Y.c3 refl) refl))
commuteFromSource Y.c3 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.c3)
      (squareOriginal Y.b1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.b1 Y.c3
        (pairMember Y.b1 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.c3)
      (squareOriginal Y.c1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.c1 Y.c3
        (pairMember Y.c1 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.c3)
      (squareOriginal Y.d1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.d1 Y.c3
        (pairMember Y.d1 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.c3)
      (squareOriginal Y.e1) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.e1 Y.c3
        (pairMember Y.e1 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.b2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.c3)
      (squareOriginal Y.b2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.b2 Y.c3
        (pairMember Y.b2 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.c2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.c3)
      (squareOriginal Y.c2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.c2 Y.c3
        (pairMember Y.c2 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.d2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.c3)
      (squareOriginal Y.d2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.d2 Y.c3
        (pairMember Y.d2 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.e2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.c3)
      (squareOriginal Y.e2) (squareOriginal Y.c3)
      (R.nonedgeProductSquare Y.e2 Y.c3
        (pairMember Y.e2 Y.c3 refl) refl))
commuteFromSource Y.c3 Y.b3 ()
commuteFromSource Y.c3 Y.c3 ()
commuteFromSource Y.c3 Y.d3 ()
commuteFromSource Y.d3 Y.a proof =
    sym (R.commuteFromThreeSquares (nodes Y.a) (nodes Y.d3)
      (squareOriginal Y.a) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.a Y.d3
        (pairMember Y.a Y.d3 refl) refl))
commuteFromSource Y.d3 Y.b1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b1) (nodes Y.d3)
      (squareOriginal Y.b1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b1 Y.d3
        (pairMember Y.b1 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.c1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c1) (nodes Y.d3)
      (squareOriginal Y.c1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.c1 Y.d3
        (pairMember Y.c1 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.d1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d1) (nodes Y.d3)
      (squareOriginal Y.d1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.d1 Y.d3
        (pairMember Y.d1 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.e1 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e1) (nodes Y.d3)
      (squareOriginal Y.e1) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.e1 Y.d3
        (pairMember Y.e1 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.b2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b2) (nodes Y.d3)
      (squareOriginal Y.b2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b2 Y.d3
        (pairMember Y.b2 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.c2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.c2) (nodes Y.d3)
      (squareOriginal Y.c2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.c2 Y.d3
        (pairMember Y.c2 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.d2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.d2) (nodes Y.d3)
      (squareOriginal Y.d2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.d2 Y.d3
        (pairMember Y.d2 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.e2 proof =
    sym (R.commuteFromThreeSquares (nodes Y.e2) (nodes Y.d3)
      (squareOriginal Y.e2) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.e2 Y.d3
        (pairMember Y.e2 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.b3 proof =
    sym (R.commuteFromThreeSquares (nodes Y.b3) (nodes Y.d3)
      (squareOriginal Y.b3) (squareOriginal Y.d3)
      (R.nonedgeProductSquare Y.b3 Y.d3
        (pairMember Y.b3 Y.d3 refl) refl))
commuteFromSource Y.d3 Y.c3 ()
commuteFromSource Y.d3 Y.d3 ()

  braidAdjacent :
    (x y : Y.Node) →
    Y.adjacent x y ≡ true →
    Pair.multiply gi (nodes x)
      (Pair.multiply gi (nodes y) (nodes x))
    ≡ Pair.multiply gi (nodes y)
      (Pair.multiply gi (nodes x) (nodes y))
  braidAdjacent Y.a Y.a ()
braidAdjacent Y.a Y.b1 proof =
    L.edgeBraid Y.a Y.b1
      (pairMember Y.a Y.b1 refl)
      (squareMember Y.a) (squareMember Y.b1) refl
braidAdjacent Y.a Y.c1 ()
braidAdjacent Y.a Y.d1 ()
braidAdjacent Y.a Y.e1 ()
braidAdjacent Y.a Y.b2 proof =
    L.edgeBraid Y.a Y.b2
      (pairMember Y.a Y.b2 refl)
      (squareMember Y.a) (squareMember Y.b2) refl
braidAdjacent Y.a Y.c2 ()
braidAdjacent Y.a Y.d2 ()
braidAdjacent Y.a Y.e2 ()
braidAdjacent Y.a Y.b3 proof =
    L.edgeBraid Y.a Y.b3
      (pairMember Y.a Y.b3 refl)
      (squareMember Y.a) (squareMember Y.b3) refl
braidAdjacent Y.a Y.c3 ()
braidAdjacent Y.a Y.d3 ()
braidAdjacent Y.b1 Y.a proof =
    sym (L.edgeBraid Y.a Y.b1
      (pairMember Y.a Y.b1 refl)
      (squareMember Y.a) (squareMember Y.b1) refl)
braidAdjacent Y.b1 Y.b1 ()
braidAdjacent Y.b1 Y.c1 proof =
    L.edgeBraid Y.b1 Y.c1
      (pairMember Y.b1 Y.c1 refl)
      (squareMember Y.b1) (squareMember Y.c1) refl
braidAdjacent Y.b1 Y.d1 ()
braidAdjacent Y.b1 Y.e1 ()
braidAdjacent Y.b1 Y.b2 ()
braidAdjacent Y.b1 Y.c2 ()
braidAdjacent Y.b1 Y.d2 ()
braidAdjacent Y.b1 Y.e2 ()
braidAdjacent Y.b1 Y.b3 ()
braidAdjacent Y.b1 Y.c3 ()
braidAdjacent Y.b1 Y.d3 ()
braidAdjacent Y.c1 Y.a ()
braidAdjacent Y.c1 Y.b1 proof =
    sym (L.edgeBraid Y.b1 Y.c1
      (pairMember Y.b1 Y.c1 refl)
      (squareMember Y.b1) (squareMember Y.c1) refl)
braidAdjacent Y.c1 Y.c1 ()
braidAdjacent Y.c1 Y.d1 proof =
    L.edgeBraid Y.c1 Y.d1
      (pairMember Y.c1 Y.d1 refl)
      (squareMember Y.c1) (squareMember Y.d1) refl
braidAdjacent Y.c1 Y.e1 ()
braidAdjacent Y.c1 Y.b2 ()
braidAdjacent Y.c1 Y.c2 ()
braidAdjacent Y.c1 Y.d2 ()
braidAdjacent Y.c1 Y.e2 ()
braidAdjacent Y.c1 Y.b3 ()
braidAdjacent Y.c1 Y.c3 ()
braidAdjacent Y.c1 Y.d3 ()
braidAdjacent Y.d1 Y.a ()
braidAdjacent Y.d1 Y.b1 ()
braidAdjacent Y.d1 Y.c1 proof =
    sym (L.edgeBraid Y.c1 Y.d1
      (pairMember Y.c1 Y.d1 refl)
      (squareMember Y.c1) (squareMember Y.d1) refl)
braidAdjacent Y.d1 Y.d1 ()
braidAdjacent Y.d1 Y.e1 proof =
    L.edgeBraid Y.d1 Y.e1
      (pairMember Y.d1 Y.e1 refl)
      (squareMember Y.d1) (squareMember Y.e1) refl
braidAdjacent Y.d1 Y.b2 ()
braidAdjacent Y.d1 Y.c2 ()
braidAdjacent Y.d1 Y.d2 ()
braidAdjacent Y.d1 Y.e2 ()
braidAdjacent Y.d1 Y.b3 ()
braidAdjacent Y.d1 Y.c3 ()
braidAdjacent Y.d1 Y.d3 ()
braidAdjacent Y.e1 Y.a ()
braidAdjacent Y.e1 Y.b1 ()
braidAdjacent Y.e1 Y.c1 ()
braidAdjacent Y.e1 Y.d1 proof =
    sym (L.edgeBraid Y.d1 Y.e1
      (pairMember Y.d1 Y.e1 refl)
      (squareMember Y.d1) (squareMember Y.e1) refl)
braidAdjacent Y.e1 Y.e1 ()
braidAdjacent Y.e1 Y.b2 ()
braidAdjacent Y.e1 Y.c2 ()
braidAdjacent Y.e1 Y.d2 ()
braidAdjacent Y.e1 Y.e2 ()
braidAdjacent Y.e1 Y.b3 ()
braidAdjacent Y.e1 Y.c3 ()
braidAdjacent Y.e1 Y.d3 ()
braidAdjacent Y.b2 Y.a proof =
    sym (L.edgeBraid Y.a Y.b2
      (pairMember Y.a Y.b2 refl)
      (squareMember Y.a) (squareMember Y.b2) refl)
braidAdjacent Y.b2 Y.b1 ()
braidAdjacent Y.b2 Y.c1 ()
braidAdjacent Y.b2 Y.d1 ()
braidAdjacent Y.b2 Y.e1 ()
braidAdjacent Y.b2 Y.b2 ()
braidAdjacent Y.b2 Y.c2 proof =
    L.edgeBraid Y.b2 Y.c2
      (pairMember Y.b2 Y.c2 refl)
      (squareMember Y.b2) (squareMember Y.c2) refl
braidAdjacent Y.b2 Y.d2 ()
braidAdjacent Y.b2 Y.e2 ()
braidAdjacent Y.b2 Y.b3 ()
braidAdjacent Y.b2 Y.c3 ()
braidAdjacent Y.b2 Y.d3 ()
braidAdjacent Y.c2 Y.a ()
braidAdjacent Y.c2 Y.b1 ()
braidAdjacent Y.c2 Y.c1 ()
braidAdjacent Y.c2 Y.d1 ()
braidAdjacent Y.c2 Y.e1 ()
braidAdjacent Y.c2 Y.b2 proof =
    sym (L.edgeBraid Y.b2 Y.c2
      (pairMember Y.b2 Y.c2 refl)
      (squareMember Y.b2) (squareMember Y.c2) refl)
braidAdjacent Y.c2 Y.c2 ()
braidAdjacent Y.c2 Y.d2 proof =
    L.edgeBraid Y.c2 Y.d2
      (pairMember Y.c2 Y.d2 refl)
      (squareMember Y.c2) (squareMember Y.d2) refl
braidAdjacent Y.c2 Y.e2 ()
braidAdjacent Y.c2 Y.b3 ()
braidAdjacent Y.c2 Y.c3 ()
braidAdjacent Y.c2 Y.d3 ()
braidAdjacent Y.d2 Y.a ()
braidAdjacent Y.d2 Y.b1 ()
braidAdjacent Y.d2 Y.c1 ()
braidAdjacent Y.d2 Y.d1 ()
braidAdjacent Y.d2 Y.e1 ()
braidAdjacent Y.d2 Y.b2 ()
braidAdjacent Y.d2 Y.c2 proof =
    sym (L.edgeBraid Y.c2 Y.d2
      (pairMember Y.c2 Y.d2 refl)
      (squareMember Y.c2) (squareMember Y.d2) refl)
braidAdjacent Y.d2 Y.d2 ()
braidAdjacent Y.d2 Y.e2 proof =
    L.edgeBraid Y.d2 Y.e2
      (pairMember Y.d2 Y.e2 refl)
      (squareMember Y.d2) (squareMember Y.e2) refl
braidAdjacent Y.d2 Y.b3 ()
braidAdjacent Y.d2 Y.c3 ()
braidAdjacent Y.d2 Y.d3 ()
braidAdjacent Y.e2 Y.a ()
braidAdjacent Y.e2 Y.b1 ()
braidAdjacent Y.e2 Y.c1 ()
braidAdjacent Y.e2 Y.d1 ()
braidAdjacent Y.e2 Y.e1 ()
braidAdjacent Y.e2 Y.b2 ()
braidAdjacent Y.e2 Y.c2 ()
braidAdjacent Y.e2 Y.d2 proof =
    sym (L.edgeBraid Y.d2 Y.e2
      (pairMember Y.d2 Y.e2 refl)
      (squareMember Y.d2) (squareMember Y.e2) refl)
braidAdjacent Y.e2 Y.e2 ()
braidAdjacent Y.e2 Y.b3 ()
braidAdjacent Y.e2 Y.c3 ()
braidAdjacent Y.e2 Y.d3 ()
braidAdjacent Y.b3 Y.a proof =
    sym (L.edgeBraid Y.a Y.b3
      (pairMember Y.a Y.b3 refl)
      (squareMember Y.a) (squareMember Y.b3) refl)
braidAdjacent Y.b3 Y.b1 ()
braidAdjacent Y.b3 Y.c1 ()
braidAdjacent Y.b3 Y.d1 ()
braidAdjacent Y.b3 Y.e1 ()
braidAdjacent Y.b3 Y.b2 ()
braidAdjacent Y.b3 Y.c2 ()
braidAdjacent Y.b3 Y.d2 ()
braidAdjacent Y.b3 Y.e2 ()
braidAdjacent Y.b3 Y.b3 ()
braidAdjacent Y.b3 Y.c3 proof =
    L.edgeBraid Y.b3 Y.c3
      (pairMember Y.b3 Y.c3 refl)
      (squareMember Y.b3) (squareMember Y.c3) refl
braidAdjacent Y.b3 Y.d3 ()
braidAdjacent Y.c3 Y.a ()
braidAdjacent Y.c3 Y.b1 ()
braidAdjacent Y.c3 Y.c1 ()
braidAdjacent Y.c3 Y.d1 ()
braidAdjacent Y.c3 Y.e1 ()
braidAdjacent Y.c3 Y.b2 ()
braidAdjacent Y.c3 Y.c2 ()
braidAdjacent Y.c3 Y.d2 ()
braidAdjacent Y.c3 Y.e2 ()
braidAdjacent Y.c3 Y.b3 proof =
    sym (L.edgeBraid Y.b3 Y.c3
      (pairMember Y.b3 Y.c3 refl)
      (squareMember Y.b3) (squareMember Y.c3) refl)
braidAdjacent Y.c3 Y.c3 ()
braidAdjacent Y.c3 Y.d3 proof =
    L.edgeBraid Y.c3 Y.d3
      (pairMember Y.c3 Y.d3 refl)
      (squareMember Y.c3) (squareMember Y.d3) refl
braidAdjacent Y.d3 Y.a ()
braidAdjacent Y.d3 Y.b1 ()
braidAdjacent Y.d3 Y.c1 ()
braidAdjacent Y.d3 Y.d1 ()
braidAdjacent Y.d3 Y.e1 ()
braidAdjacent Y.d3 Y.b2 ()
braidAdjacent Y.d3 Y.c2 ()
braidAdjacent Y.d3 Y.d2 ()
braidAdjacent Y.d3 Y.e2 ()
braidAdjacent Y.d3 Y.b3 ()
braidAdjacent Y.d3 Y.c3 proof =
    sym (L.edgeBraid Y.c3 Y.d3
      (pairMember Y.c3 Y.d3 refl)
      (squareMember Y.c3) (squareMember Y.d3) refl)
braidAdjacent Y.d3 Y.d3 ()

  braidFromSource :
    (x y z : Y.Node) →
    Finite.canBraid x y z ≡ true →
    Pair.multiply gi (nodes x)
      (Pair.multiply gi (nodes y) (nodes z))
    ≡ Pair.multiply gi (nodes y)
      (Pair.multiply gi (nodes x) (nodes y))
  braidFromSource x y z condition
    with eqNodeSound x z
      (andLeftTrue (Finite.eqNode x z) (Y.adjacent x y) condition)
  ... | refl =
    braidAdjacent x y
      (andRightTrue (Finite.eqNode x x) (Y.adjacent x y) condition)

  allGraphLaws : Path.GraphCoxeterGroupLaws gi nodes
  allGraphLaws = record
    { Path.square = squareOriginal
    ; Path.commute = commuteFromSource
    ; Path.braid = braidFromSource
    }

  allElevenShiftsFromActual80 :
    All.JMDPathShiftCertificate
      gi nodes
  allElevenShiftsFromActual80 =
    Path.Semantic.elevenSourcePathShiftEquations
      gi nodes all allGraphLaws

  ------------------------------------------------------------------------
  -- The genuine all-node JMD word certificate follows from the SAME
  -- original 80-relator witness, without a second path-shift assumption.
  -- It does not prove that the selected group IS the presented quotient.
  ------------------------------------------------------------------------

  module Recovered = All.Recover gi nodes all allElevenShiftsFromActual80

  allTwelveNodeWordsFromActual80 :
    Pair.NodeWordCertificate gi
      (Words.uElement gi nodes)
      (Words.vElement gi nodes)
      nodes
  allTwelveNodeWordsFromActual80 =
    Recovered.actualNodeWordCertificate
