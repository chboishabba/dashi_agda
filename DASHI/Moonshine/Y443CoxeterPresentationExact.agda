module DASHI.Moonshine.Y443CoxeterPresentationExact where

------------------------------------------------------------------------
-- The Y_443 Coxeter/spider presentation: exact finite source transcription.
--
-- SOURCE OWNERS:
-- A. A. Ivanov, "Y-groups via Transitive Extension", J. Algebra 218
-- (1999), 412--435, doi:10.1006/jabr.1999.7882.
-- J. N. Bray, "Sporadic (Fischer--Griess) Monster group M = F_1",
-- presentation of M x C2 by Y_443 with the spider relator.
-- The TauCeti formal Monster presentation is an independent Lean donor:
-- https://taucetiproject.org/docs/TauCeti/GroupTheory/SpecificGroups/CFSG/Sporadic/Monster.html
--
-- JMD / James Michael DuPont (meta-introspector) owns the separate
-- two-generator H = <u,v> generation report/trace. Its unprovided path
-- words and kernel certificate are NOT silently reconstructed here.
--
-- DASHI CONTRIBUTION:
-- A self-contained finite alphabet, graph, Coxeter relator word list,
-- spider and Ivanov f_312 word, with executable Agda equalities for
-- twelve nodes, eleven edges, 55 nonedges, 79/80 relators, and exact
-- written lengths 400/463. This module DOES NOT assert a group
-- isomorphism, an order, or the JMD two-generator theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {A : Set} → List A → Nat
length [] = 0
length (_ ∷ xs) = suc (length xs)

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

------------------------------------------------------------------------
-- Central vertex + arms of lengths 4, 4, 3.
------------------------------------------------------------------------

data Node : Set where
  a b1 c1 d1 e1 b2 c2 d2 e2 b3 c3 d3 : Node

nodes : List Node
nodes =
  a ∷ b1 ∷ c1 ∷ d1 ∷ e1 ∷
  b2 ∷ c2 ∷ d2 ∷ e2 ∷
  b3 ∷ c3 ∷ d3 ∷ []

nodeCount : length nodes ≡ 12
nodeCount = refl

-- The adjacency relation is symmetric and has no loops.
adjacent : Node → Node → Bool
adjacent a b1 = true
adjacent b1 a = true
adjacent b1 c1 = true
adjacent c1 b1 = true
adjacent c1 d1 = true
adjacent d1 c1 = true
adjacent d1 e1 = true
adjacent e1 d1 = true

adjacent a b2 = true
adjacent b2 a = true
adjacent b2 c2 = true
adjacent c2 b2 = true
adjacent c2 d2 = true
adjacent d2 c2 = true
adjacent d2 e2 = true
adjacent e2 d2 = true

adjacent a b3 = true
adjacent b3 a = true
adjacent b3 c3 = true
adjacent c3 b3 = true
adjacent c3 d3 = true
adjacent d3 c3 = true
adjacent _ _ = false

record Pair : Set where
  constructor pair
  field
    first second : Node
open Pair public

pairsFrom : Node → List Node → List Pair
pairsFrom x [] = []
pairsFrom x (y ∷ ys) = pair x y ∷ pairsFrom x ys

unorderedPairs : List Node → List Pair
unorderedPairs [] = []
unorderedPairs (x ∷ xs) = pairsFrom x xs ++ unorderedPairs xs

pairs : List Pair
pairs = unorderedPairs nodes

pairCount : length pairs ≡ 66
pairCount = refl

edgeIndicator : Bool → Nat
edgeIndicator true = 1
edgeIndicator false = 0

nonedgeIndicator : Bool → Nat
nonedgeIndicator true = 0
nonedgeIndicator false = 1

countEdges : List Pair → Nat
countEdges [] = 0
countEdges (p ∷ ps) =
  edgeIndicator (adjacent (first p) (second p)) + countEdges ps

countNonedges : List Pair → Nat
countNonedges [] = 0
countNonedges (p ∷ ps) =
  nonedgeIndicator (adjacent (first p) (second p)) + countNonedges ps

elevenEdges : countEdges pairs ≡ 11
elevenEdges = refl

fiftyFiveNonedges : countNonedges pairs ≡ 55
fiftyFiveNonedges = refl

------------------------------------------------------------------------
-- Relators are positive words: each generator is an involution.
-- For nonadjacent nodes (xy)^2=1; for adjacent nodes (xy)^3=1.
------------------------------------------------------------------------

Word : Set
Word = List Node

powerWord : Word → Nat → Word
powerWord word zero = []
powerWord word (suc n) = word ++ powerWord word n

square : Node → Word
square x = x ∷ x ∷ []

pairExponent : Bool → Nat
pairExponent true = 3
pairExponent false = 2

pairRelator : Pair → Word
pairRelator p =
  powerWord (first p ∷ second p ∷ [])
    (pairExponent (adjacent (first p) (second p)))

coxeterRelators : List Word
coxeterRelators = map square nodes ++ map pairRelator pairs

coxeterRelatorCount : length coxeterRelators ≡ 78
coxeterRelatorCount = refl

wordLengthSum : List Word → Nat
wordLengthSum [] = 0
wordLengthSum (word ∷ rest) = length word + wordLengthSum rest

coxeterWrittenLength : wordLengthSum coxeterRelators ≡ 310
coxeterWrittenLength = refl

-- (a b1 c1 a b2 c2 a b3 c3)^10 = 1.
spiderBase : Word
spiderBase = a ∷ b1 ∷ c1 ∷ a ∷ b2 ∷ c2 ∷ a ∷ b3 ∷ c3 ∷ []

spiderRelator : Word
spiderRelator = powerWord spiderBase 10

spiderLength : length spiderRelator ≡ 90
spiderLength = refl

-- Ivanov's f_312 = (a b3 c3 d3 b1 c1 b2)^9.
-- Identifying this word as a central involution is a separate group theorem.
centralBase : Word
centralBase = a ∷ b3 ∷ c3 ∷ d3 ∷ b1 ∷ c1 ∷ b2 ∷ []

centralInvolutionRelator : Word
centralInvolutionRelator = powerWord centralBase 9

centralRelatorLength : length centralInvolutionRelator ≡ 63
centralRelatorLength = refl

doubleMonsterRelators : List Word
doubleMonsterRelators = coxeterRelators ++ (spiderRelator ∷ [])

monsterRelators : List Word
monsterRelators = doubleMonsterRelators ++ (centralInvolutionRelator ∷ [])

doubleMonsterRelatorCount : length doubleMonsterRelators ≡ 79
doubleMonsterRelatorCount = refl

monsterRelatorCount : length monsterRelators ≡ 80
monsterRelatorCount = refl

doubleMonsterWrittenLength :
  wordLengthSum doubleMonsterRelators ≡ 400
doubleMonsterWrittenLength = refl

monsterWrittenLength : wordLengthSum monsterRelators ≡ 463
monsterWrittenLength = refl

-- The twelve standard Coxeter involutions are a separate alphabet from the
-- dimension-twelve Suzuki constituent or the 12 axes of the Heisenberg model.
data TwelveRole : Set where
  coxeterInvolutionAlphabet : TwelveRole
  suzukiDegreeTwelve : TwelveRole
  heisenbergSixPlusSix : TwelveRole

open import Agda.Builtin.Unit using (⊤)

distinctTwelveRoles :
  coxeterInvolutionAlphabet ≡ suzukiDegreeTwelve → ⊤
distinctTwelveRoles ()
