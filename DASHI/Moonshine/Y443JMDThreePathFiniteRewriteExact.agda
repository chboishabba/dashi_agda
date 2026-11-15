module DASHI.Moonshine.Y443JMDThreePathFiniteRewriteExact where

------------------------------------------------------------------------
-- ALL ELEVEN SOURCE-EXACT COXETER PATH SHIFT CERTIFICATES.
-- A generator in the selected Coxeter presentation is an involution.
--
-- For the first JMD path P1=[d3,c3,b3,a,b1,c1,d1,e1],
--  reverse(P1) P1[i+1] P1  -> P1[i], 0<=i<7,
-- using seven native 15-move Coxeter rewrite certificates.
--
-- For the third JMD path P3=[a,b2,c2,d2,e2],
--  P3 P3[i] reverse(P3) -> P3[i+1], 0<=i<4,
-- using four native 9-move Coxeter rewrite certificates.
--
-- All 11 are checked by evaluating each exact local rewrite using the
-- ORIGINAL 12-node Y443 graph adjacency and canonical node equality.
-- No external "pathShift" equality is inserted in this finite layer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Moonshine.Y443CoxeterPresentationExact as Y
import DASHI.Moonshine.Y443JMDSourceWordInstantiationExact as JMD
import DASHI.Moonshine.Y443JMDBetaFiveFiniteRewriteExact as W
import DASHI.Moonshine.Y443JMDThreePathGraphCertificateExact as Graph

eqNode : Y.Node → Y.Node → Bool
eqNode = Graph.eqNode

notB : Bool → Bool
notB true = false
notB false = true

andB : Bool → Bool → Bool
andB true true = true
andB _ _ = false

canCommute : Y.Node → Y.Node → Bool
canCommute a b = andB (notB (eqNode a b)) (notB (Y.adjacent a b))

canBraid : Y.Node → Y.Node → Y.Node → Bool
canBraid a b c = andB (eqNode a c) (Y.adjacent a b)

validLocal : W.Kind → Y.Word → Bool
validLocal W.cancel (a ∷ b ∷ _) = eqNode a b
validLocal W.commute (a ∷ b ∷ _) = canCommute a b
validLocal W.braid (a ∷ b ∷ c ∷ _) = canBraid a b c
validLocal _ _ = false

rewriteLocal : W.Kind → Y.Word → Y.Word
rewriteLocal W.cancel (a ∷ b ∷ rest) with eqNode a b
... | true = rest
... | false = a ∷ b ∷ rest
rewriteLocal W.commute (a ∷ b ∷ rest) with canCommute a b
... | true = b ∷ a ∷ rest
... | false = a ∷ b ∷ rest
rewriteLocal W.braid (a ∷ b ∷ c ∷ rest) with canBraid a b c
... | true = b ∷ a ∷ b ∷ rest
... | false = a ∷ b ∷ c ∷ rest
rewriteLocal _ word = word

validAt : Nat → W.Kind → Y.Word → Bool
validAt zero rule word = validLocal rule word
validAt (suc n) rule [] = false
validAt (suc n) rule (_ ∷ rest) = validAt n rule rest

stepAt : Nat → W.Kind → Y.Word → Y.Word
stepAt zero rule word = rewriteLocal rule word
stepAt (suc n) rule [] = []
stepAt (suc n) rule (x ∷ rest) = x ∷ stepAt n rule rest

step : W.Operation → Y.Word → Y.Word
step op = stepAt (W.position op) (W.kind op)

run : Y.Word → List W.Operation → Y.Word
run word [] = word
run word (op ∷ rest) = run (step op word) rest

everyStepValid : Y.Word → List W.Operation → Bool
everyStepValid word [] = true
everyStepValid word (op ∷ rest) =
  andB (validAt (W.position op) (W.kind op) word)
    (everyStepValid (step op word) rest)

reverse : Y.Word → Y.Word
reverse [] = []
reverse (a ∷ rest) = Y._++_ (reverse rest) (a ∷ [])

lookupPath : Y.Word → Nat → Y.Node
lookupPath [] _ = Y.a
lookupPath (x ∷ xs) zero = x
lookupPath (x ∷ xs) (suc n) = lookupPath xs n

firstPath : Y.Word
firstPath = JMD.uPath

thirdPath : Y.Word
thirdPath = JMD.thirdPath

backwardWord : Nat → Y.Word
backwardWord i =
  Y._++_ (reverse firstPath)
    (Y._++_ (lookupPath firstPath (suc i) ∷ []) firstPath)

forwardWord : Nat → Y.Word
forwardWord i =
  Y._++_ thirdPath
    (Y._++_ (lookupPath thirdPath i ∷ []) (reverse thirdPath))

pathP1Shift0 : List W.Operation
pathP1Shift0 =
  W.operation W.braid 6 ∷
  W.operation W.commute 5 ∷
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift0Valid :
  everyStepValid (backwardWord 0) pathP1Shift0 ≡ true
pathP1Shift0Valid = refl

pathP1Shift0Result :
  run (backwardWord 0) pathP1Shift0
  ≡ (lookupPath firstPath 0 ∷ [])
pathP1Shift0Result = refl

pathP1Shift1 : List W.Operation
pathP1Shift1 =
  W.operation W.commute 7 ∷
  W.operation W.braid 5 ∷
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift1Valid :
  everyStepValid (backwardWord 1) pathP1Shift1 ≡ true
pathP1Shift1Valid = refl

pathP1Shift1Result :
  run (backwardWord 1) pathP1Shift1
  ≡ (lookupPath firstPath 1 ∷ [])
pathP1Shift1Result = refl

pathP1Shift2 : List W.Operation
pathP1Shift2 =
  W.operation W.commute 7 ∷
  W.operation W.commute 6 ∷
  W.operation W.braid 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift2Valid :
  everyStepValid (backwardWord 2) pathP1Shift2 ≡ true
pathP1Shift2Valid = refl

pathP1Shift2Result :
  run (backwardWord 2) pathP1Shift2
  ≡ (lookupPath firstPath 2 ∷ [])
pathP1Shift2Result = refl

pathP1Shift3 : List W.Operation
pathP1Shift3 =
  W.operation W.commute 7 ∷
  W.operation W.commute 6 ∷
  W.operation W.commute 5 ∷
  W.operation W.braid 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift3Valid :
  everyStepValid (backwardWord 3) pathP1Shift3 ≡ true
pathP1Shift3Valid = refl

pathP1Shift3Result :
  run (backwardWord 3) pathP1Shift3
  ≡ (lookupPath firstPath 3 ∷ [])
pathP1Shift3Result = refl

pathP1Shift4 : List W.Operation
pathP1Shift4 =
  W.operation W.commute 7 ∷
  W.operation W.commute 6 ∷
  W.operation W.commute 5 ∷
  W.operation W.commute 4 ∷
  W.operation W.braid 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift4Valid :
  everyStepValid (backwardWord 4) pathP1Shift4 ≡ true
pathP1Shift4Valid = refl

pathP1Shift4Result :
  run (backwardWord 4) pathP1Shift4
  ≡ (lookupPath firstPath 4 ∷ [])
pathP1Shift4Result = refl

pathP1Shift5 : List W.Operation
pathP1Shift5 =
  W.operation W.commute 7 ∷
  W.operation W.commute 6 ∷
  W.operation W.commute 5 ∷
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.braid 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift5Valid :
  everyStepValid (backwardWord 5) pathP1Shift5 ≡ true
pathP1Shift5Valid = refl

pathP1Shift5Result :
  run (backwardWord 5) pathP1Shift5
  ≡ (lookupPath firstPath 5 ∷ [])
pathP1Shift5Result = refl

pathP1Shift6 : List W.Operation
pathP1Shift6 =
  W.operation W.commute 7 ∷
  W.operation W.commute 6 ∷
  W.operation W.commute 5 ∷
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.braid 0 ∷
  W.operation W.cancel 8 ∷
  W.operation W.cancel 7 ∷
  W.operation W.cancel 6 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP1Shift6Valid :
  everyStepValid (backwardWord 6) pathP1Shift6 ≡ true
pathP1Shift6Valid = refl

pathP1Shift6Result :
  run (backwardWord 6) pathP1Shift6
  ≡ (lookupPath firstPath 6 ∷ [])
pathP1Shift6Result = refl

pathP3Shift0 : List W.Operation
pathP3Shift0 =
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.braid 0 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP3Shift0Valid :
  everyStepValid (forwardWord 0) pathP3Shift0 ≡ true
pathP3Shift0Valid = refl

pathP3Shift0Result :
  run (forwardWord 0) pathP3Shift0
  ≡ (lookupPath thirdPath 1 ∷ [])
pathP3Shift0Result = refl

pathP3Shift1 : List W.Operation
pathP3Shift1 =
  W.operation W.commute 4 ∷
  W.operation W.commute 3 ∷
  W.operation W.braid 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP3Shift1Valid :
  everyStepValid (forwardWord 1) pathP3Shift1 ≡ true
pathP3Shift1Valid = refl

pathP3Shift1Result :
  run (forwardWord 1) pathP3Shift1
  ≡ (lookupPath thirdPath 2 ∷ [])
pathP3Shift1Result = refl

pathP3Shift2 : List W.Operation
pathP3Shift2 =
  W.operation W.commute 4 ∷
  W.operation W.braid 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP3Shift2Valid :
  everyStepValid (forwardWord 2) pathP3Shift2 ≡ true
pathP3Shift2Valid = refl

pathP3Shift2Result :
  run (forwardWord 2) pathP3Shift2
  ≡ (lookupPath thirdPath 3 ∷ [])
pathP3Shift2Result = refl

pathP3Shift3 : List W.Operation
pathP3Shift3 =
  W.operation W.braid 3 ∷
  W.operation W.commute 2 ∷
  W.operation W.commute 1 ∷
  W.operation W.commute 0 ∷
  W.operation W.cancel 5 ∷
  W.operation W.cancel 4 ∷
  W.operation W.cancel 3 ∷
  W.operation W.cancel 2 ∷
  W.operation W.cancel 1 ∷
  []

pathP3Shift3Valid :
  everyStepValid (forwardWord 3) pathP3Shift3 ≡ true
pathP3Shift3Valid = refl

pathP3Shift3Result :
  run (forwardWord 3) pathP3Shift3
  ≡ (lookupPath thirdPath 4 ∷ [])
pathP3Shift3Result = refl

