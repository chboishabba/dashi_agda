module DASHI.Mathematics.Complexity.PNPGolay729HyperbolicExact where

-- Actual systematic [12,6,6]_3 generator from ExplicitCode729, not a
-- second hand-coded generator. The new complement is for the polar form
-- of Q(x)=sum_{i<j} x_i*x_j, not a claim about all 729 carriers.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Vec.Base using (Vec; []; _∷_; lookup)
import DASHI.Foundations.Base369TriTruthField as F
import DASHI.Foundations.TernaryGolay.ExplicitCode729 as G
import DASHI.Foundations.TernaryGolay.CodeBoundary as C

Word : Set
Word = C.Word12

sumWord : Word → TriTruth
sumWord x = F.triAdd
  (G.add6 (C.e0 x) (C.e1 x) (C.e2 x) (C.e3 x) (C.e4 x) (C.e5 x))
  (G.add6 (C.e6 x) (C.e7 x) (C.e8 x) (C.e9 x) (C.e10 x) (C.e11 x))

polar : Word → Word → TriTruth
polar x y = F.triAdd (F.triMul (sumWord x) (sumWord y)) (F.triNeg (G.dot x y))

plus : Word → Word → Word
plus x y = C.vec12
  (F.triAdd (C.e0 x) (C.e0 y))
  (F.triAdd (C.e1 x) (C.e1 y))
  (F.triAdd (C.e2 x) (C.e2 y))
  (F.triAdd (C.e3 x) (C.e3 y))
  (F.triAdd (C.e4 x) (C.e4 y))
  (F.triAdd (C.e5 x) (C.e5 y))
  (F.triAdd (C.e6 x) (C.e6 y))
  (F.triAdd (C.e7 x) (C.e7 y))
  (F.triAdd (C.e8 x) (C.e8 y))
  (F.triAdd (C.e9 x) (C.e9 y))
  (F.triAdd (C.e10 x) (C.e10 y))
  (F.triAdd (C.e11 x) (C.e11 y))

zeroWord : Word
zeroWord = C.vec12 tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low

g0 : Word
g0 = G.encode G.basis0

g1 : Word
g1 = G.encode G.basis1

g2 : Word
g2 = G.encode G.basis2

g3 : Word
g3 = G.encode G.basis3

g4 : Word
g4 = G.encode G.basis4

g5 : Word
g5 = G.encode G.basis5

h0 : Word
h0 = plus (C.vec12 tri-high tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g1 (plus g2 (plus g3 (plus g4 (plus g5 (zeroWord))))))

h1 : Word
h1 = plus (C.vec12 tri-low tri-high tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g0 (plus g2 (plus g3 (plus g4 (plus g5 (zeroWord))))))

h2 : Word
h2 = plus (C.vec12 tri-low tri-low tri-high tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g0 (plus g1 (plus g3 (plus g4 (plus g5 (zeroWord))))))

h3 : Word
h3 = plus (C.vec12 tri-low tri-low tri-low tri-high tri-low tri-low tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g0 (plus g1 (plus g2 (plus g4 (plus g5 (zeroWord))))))

h4 : Word
h4 = plus (C.vec12 tri-low tri-low tri-low tri-low tri-high tri-low tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g0 (plus g1 (plus g2 (plus g3 (plus g5 (zeroWord))))))

h5 : Word
h5 = plus (C.vec12 tri-low tri-low tri-low tri-low tri-low tri-high tri-low tri-low tri-low tri-low tri-low tri-low)
  (plus g0 (plus g1 (plus g2 (plus g3 (plus g4 (zeroWord))))))

gs hs : Vec Word 6
gs = g0 ∷ g1 ∷ g2 ∷ g3 ∷ g4 ∷ g5 ∷ []
hs = h0 ∷ h1 ∷ h2 ∷ h3 ∷ h4 ∷ h5 ∷ []

delta : ∀ {n} → Fin n → Fin n → TriTruth
delta zero zero = tri-mid
delta zero (suc _) = tri-low
delta (suc _) zero = tri-low
delta (suc i) (suc j) = delta i j

rowSumZero : ∀ i → sumWord (lookup gs i) ≡ tri-low
rowSumZero (zero) = refl
rowSumZero (suc zero) = refl
rowSumZero (suc suc zero) = refl
rowSumZero (suc suc suc zero) = refl
rowSumZero (suc suc suc suc zero) = refl
rowSumZero (suc suc suc suc suc zero) = refl

gGram : ∀ i j → polar (lookup gs i) (lookup gs j) ≡ tri-low
gGram (zero) (zero) = refl
gGram (zero) (suc zero) = refl
gGram (zero) (suc suc zero) = refl
gGram (zero) (suc suc suc zero) = refl
gGram (zero) (suc suc suc suc zero) = refl
gGram (zero) (suc suc suc suc suc zero) = refl
gGram (suc zero) (zero) = refl
gGram (suc zero) (suc zero) = refl
gGram (suc zero) (suc suc zero) = refl
gGram (suc zero) (suc suc suc zero) = refl
gGram (suc zero) (suc suc suc suc zero) = refl
gGram (suc zero) (suc suc suc suc suc zero) = refl
gGram (suc suc zero) (zero) = refl
gGram (suc suc zero) (suc zero) = refl
gGram (suc suc zero) (suc suc zero) = refl
gGram (suc suc zero) (suc suc suc zero) = refl
gGram (suc suc zero) (suc suc suc suc zero) = refl
gGram (suc suc zero) (suc suc suc suc suc zero) = refl
gGram (suc suc suc zero) (zero) = refl
gGram (suc suc suc zero) (suc zero) = refl
gGram (suc suc suc zero) (suc suc zero) = refl
gGram (suc suc suc zero) (suc suc suc zero) = refl
gGram (suc suc suc zero) (suc suc suc suc zero) = refl
gGram (suc suc suc zero) (suc suc suc suc suc zero) = refl
gGram (suc suc suc suc zero) (zero) = refl
gGram (suc suc suc suc zero) (suc zero) = refl
gGram (suc suc suc suc zero) (suc suc zero) = refl
gGram (suc suc suc suc zero) (suc suc suc zero) = refl
gGram (suc suc suc suc zero) (suc suc suc suc zero) = refl
gGram (suc suc suc suc zero) (suc suc suc suc suc zero) = refl
gGram (suc suc suc suc suc zero) (zero) = refl
gGram (suc suc suc suc suc zero) (suc zero) = refl
gGram (suc suc suc suc suc zero) (suc suc zero) = refl
gGram (suc suc suc suc suc zero) (suc suc suc zero) = refl
gGram (suc suc suc suc suc zero) (suc suc suc suc zero) = refl
gGram (suc suc suc suc suc zero) (suc suc suc suc suc zero) = refl

hGram : ∀ i j → polar (lookup hs i) (lookup hs j) ≡ tri-low
hGram (zero) (zero) = refl
hGram (zero) (suc zero) = refl
hGram (zero) (suc suc zero) = refl
hGram (zero) (suc suc suc zero) = refl
hGram (zero) (suc suc suc suc zero) = refl
hGram (zero) (suc suc suc suc suc zero) = refl
hGram (suc zero) (zero) = refl
hGram (suc zero) (suc zero) = refl
hGram (suc zero) (suc suc zero) = refl
hGram (suc zero) (suc suc suc zero) = refl
hGram (suc zero) (suc suc suc suc zero) = refl
hGram (suc zero) (suc suc suc suc suc zero) = refl
hGram (suc suc zero) (zero) = refl
hGram (suc suc zero) (suc zero) = refl
hGram (suc suc zero) (suc suc zero) = refl
hGram (suc suc zero) (suc suc suc zero) = refl
hGram (suc suc zero) (suc suc suc suc zero) = refl
hGram (suc suc zero) (suc suc suc suc suc zero) = refl
hGram (suc suc suc zero) (zero) = refl
hGram (suc suc suc zero) (suc zero) = refl
hGram (suc suc suc zero) (suc suc zero) = refl
hGram (suc suc suc zero) (suc suc suc zero) = refl
hGram (suc suc suc zero) (suc suc suc suc zero) = refl
hGram (suc suc suc zero) (suc suc suc suc suc zero) = refl
hGram (suc suc suc suc zero) (zero) = refl
hGram (suc suc suc suc zero) (suc zero) = refl
hGram (suc suc suc suc zero) (suc suc zero) = refl
hGram (suc suc suc suc zero) (suc suc suc zero) = refl
hGram (suc suc suc suc zero) (suc suc suc suc zero) = refl
hGram (suc suc suc suc zero) (suc suc suc suc suc zero) = refl
hGram (suc suc suc suc suc zero) (zero) = refl
hGram (suc suc suc suc suc zero) (suc zero) = refl
hGram (suc suc suc suc suc zero) (suc suc zero) = refl
hGram (suc suc suc suc suc zero) (suc suc suc zero) = refl
hGram (suc suc suc suc suc zero) (suc suc suc suc zero) = refl
hGram (suc suc suc suc suc zero) (suc suc suc suc suc zero) = refl

crossGram : ∀ i j → polar (lookup gs i) (lookup hs j) ≡ delta i j
crossGram (zero) (zero) = refl
crossGram (zero) (suc zero) = refl
crossGram (zero) (suc suc zero) = refl
crossGram (zero) (suc suc suc zero) = refl
crossGram (zero) (suc suc suc suc zero) = refl
crossGram (zero) (suc suc suc suc suc zero) = refl
crossGram (suc zero) (zero) = refl
crossGram (suc zero) (suc zero) = refl
crossGram (suc zero) (suc suc zero) = refl
crossGram (suc zero) (suc suc suc zero) = refl
crossGram (suc zero) (suc suc suc suc zero) = refl
crossGram (suc zero) (suc suc suc suc suc zero) = refl
crossGram (suc suc zero) (zero) = refl
crossGram (suc suc zero) (suc zero) = refl
crossGram (suc suc zero) (suc suc zero) = refl
crossGram (suc suc zero) (suc suc suc zero) = refl
crossGram (suc suc zero) (suc suc suc suc zero) = refl
crossGram (suc suc zero) (suc suc suc suc suc zero) = refl
crossGram (suc suc suc zero) (zero) = refl
crossGram (suc suc suc zero) (suc zero) = refl
crossGram (suc suc suc zero) (suc suc zero) = refl
crossGram (suc suc suc zero) (suc suc suc zero) = refl
crossGram (suc suc suc zero) (suc suc suc suc zero) = refl
crossGram (suc suc suc zero) (suc suc suc suc suc zero) = refl
crossGram (suc suc suc suc zero) (zero) = refl
crossGram (suc suc suc suc zero) (suc zero) = refl
crossGram (suc suc suc suc zero) (suc suc zero) = refl
crossGram (suc suc suc suc zero) (suc suc suc zero) = refl
crossGram (suc suc suc suc zero) (suc suc suc suc zero) = refl
crossGram (suc suc suc suc zero) (suc suc suc suc suc zero) = refl
crossGram (suc suc suc suc suc zero) (zero) = refl
crossGram (suc suc suc suc suc zero) (suc zero) = refl
crossGram (suc suc suc suc suc zero) (suc suc zero) = refl
crossGram (suc suc suc suc suc zero) (suc suc suc zero) = refl
crossGram (suc suc suc suc suc zero) (suc suc suc suc zero) = refl
crossGram (suc suc suc suc suc zero) (suc suc suc suc suc zero) = refl

messageCount : G.listCount G.allMessages ≡ 729
messageCount = G.allMessagesCountIs729
