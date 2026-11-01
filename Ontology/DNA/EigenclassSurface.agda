module Ontology.DNA.EigenclassSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Vec using (Vec; []; _∷_)

open import Ontology.DNA.Supervoxel4Adic using (Base; A; C; G; T)
open import Ontology.DNA.ChemistryQuotient using
  (Strength; PurineClass; strength; purineClass)
open import Ontology.DNA.ChemistryConcrete using (_&&_; baseEq)

------------------------------------------------------------------------
-- Eigenclass and macro-adjacency surface.
-- This owns the "what is the symbol/eigenclass of a block?" question and the
-- first exact macro-adjacency rule over a six-line bundle.

DNA3 : Set
DNA3 = Vec Base 3

DNA6x3 : Set
DNA6x3 = Vec DNA3 6

data ScanOrder : Set where
  lineMajor layerMajor : ScanOrder

record EigenClass3 : Set where
  constructor eigenClass3
  field
    uSignature : Vec Strength 3
    vSignature : Vec PurineClass 3
    lineAdmissible : Bool

neqBase : Base → Base → Bool
neqBase x y with baseEq x y
... | true = false
... | false = true

neqBase-sym : ∀ (x y : Base) → neqBase x y ≡ neqBase y x
neqBase-sym A A = refl
neqBase-sym A C = refl
neqBase-sym A G = refl
neqBase-sym A T = refl
neqBase-sym C A = refl
neqBase-sym C C = refl
neqBase-sym C G = refl
neqBase-sym C T = refl
neqBase-sym G A = refl
neqBase-sym G C = refl
neqBase-sym G G = refl
neqBase-sym G T = refl
neqBase-sym T A = refl
neqBase-sym T C = refl
neqBase-sym T G = refl
neqBase-sym T T = refl

allDistinct3 : Base → Base → Base → Bool
allDistinct3 a b c =
  neqBase a b && (neqBase b c && neqBase a c)

classify3 : DNA3 → EigenClass3
classify3 (a ∷ b ∷ c ∷ []) =
  eigenClass3
    (strength a ∷ strength b ∷ strength c ∷ [])
    (purineClass a ∷ purineClass b ∷ purineClass c ∷ [])
    (allDistinct3 a b c)

classify3-uSignature-exact :
  ∀ (a b c : Base) →
  EigenClass3.uSignature (classify3 (a ∷ b ∷ c ∷ []))
    ≡ strength a ∷ strength b ∷ strength c ∷ []
classify3-uSignature-exact a b c = refl

classify3-vSignature-exact :
  ∀ (a b c : Base) →
  EigenClass3.vSignature (classify3 (a ∷ b ∷ c ∷ []))
    ≡ purineClass a ∷ purineClass b ∷ purineClass c ∷ []
classify3-vSignature-exact a b c = refl

eigenRepresentative3 : DNA3 → Bool
eigenRepresentative3 (a ∷ b ∷ c ∷ []) =
  allDistinct3 a b c

classify3-lineAdmissible-consistent :
  ∀ (xs : DNA3) →
  EigenClass3.lineAdmissible (classify3 xs) ≡ eigenRepresentative3 xs
classify3-lineAdmissible-consistent (a ∷ b ∷ c ∷ []) = refl

macroAdjacency2 : DNA3 → DNA3 → Bool
macroAdjacency2 (a₁ ∷ a₂ ∷ a₃ ∷ []) (b₁ ∷ b₂ ∷ b₃ ∷ []) =
  neqBase a₁ b₁ && (neqBase a₂ b₂ && neqBase a₃ b₃)

macroAdjacency2-sym :
  ∀ (xs ys : DNA3) →
  macroAdjacency2 xs ys ≡ macroAdjacency2 ys xs
macroAdjacency2-sym
  (a₁ ∷ a₂ ∷ a₃ ∷ [])
  (b₁ ∷ b₂ ∷ b₃ ∷ [])
  rewrite neqBase-sym a₁ b₁
        | neqBase-sym a₂ b₂
        | neqBase-sym a₃ b₃ = refl

boolToNat : Bool → Nat
boolToNat true = suc zero
boolToNat false = zero

boolToNat-suc :
  ∀ (b : Bool) →
  suc (boolToNat b) ≡ boolToNat true + boolToNat b
boolToNat-suc true = refl
boolToNat-suc false = refl

countMacroAdjacency6From : ∀ {n} → DNA3 → Vec DNA3 n → Nat
countMacroAdjacency6From x [] = zero
countMacroAdjacency6From x (y ∷ ys) with macroAdjacency2 x y
... | true  = suc (countMacroAdjacency6From y ys)
... | false = countMacroAdjacency6From y ys

countMacroAdjacency : ∀ {n} → Vec DNA3 n → Nat
countMacroAdjacency [] = zero
countMacroAdjacency (x ∷ xs) = countMacroAdjacency6From x xs

countMacroAdjacency6 : DNA6x3 → Nat
countMacroAdjacency6 xs = countMacroAdjacency xs

countMacroAdjacency6From-singleton :
  ∀ (x y : DNA3) →
  countMacroAdjacency6From x (y ∷ []) ≡ boolToNat (macroAdjacency2 x y)
countMacroAdjacency6From-singleton x y with macroAdjacency2 x y
... | true = refl
... | false = refl

countMacroAdjacency-pair-exact :
  ∀ (x y : DNA3) →
  countMacroAdjacency (x ∷ y ∷ []) ≡ boolToNat (macroAdjacency2 x y)
countMacroAdjacency-pair-exact x y = countMacroAdjacency6From-singleton x y

countMacroAdjacency-pair-sym :
  ∀ (x y : DNA3) →
  countMacroAdjacency (x ∷ y ∷ []) ≡ countMacroAdjacency (y ∷ x ∷ [])
countMacroAdjacency-pair-sym x y
  rewrite countMacroAdjacency-pair-exact x y
        | countMacroAdjacency-pair-exact y x
        | macroAdjacency2-sym x y = refl

countMacroAdjacency-triple-step :
  ∀ (x y z : DNA3) →
  countMacroAdjacency (x ∷ y ∷ z ∷ [])
    ≡ boolToNat (macroAdjacency2 x y) + boolToNat (macroAdjacency2 y z)
countMacroAdjacency-triple-step x y z with macroAdjacency2 x y
... | true with macroAdjacency2 y z
...   | true
  rewrite countMacroAdjacency6From-singleton y z
        | boolToNat-suc true = refl
...   | false
  rewrite countMacroAdjacency6From-singleton y z
        | boolToNat-suc false = refl
countMacroAdjacency-triple-step x y z | false with macroAdjacency2 y z
... | true = refl
... | false = refl

record MacroAdjacencySurface : Set where
  constructor macroAdjacencySurface
  field
    scanOrder : ScanOrder
    coupledAdjacency : Bool
    adjacencyScore : Nat

macroSurface : DNA6x3 → MacroAdjacencySurface
macroSurface xs =
  macroAdjacencySurface lineMajor true (countMacroAdjacency6 xs)

macroSurface-score-exact :
  ∀ (xs : DNA6x3) →
  MacroAdjacencySurface.adjacencyScore (macroSurface xs) ≡ countMacroAdjacency6 xs
macroSurface-score-exact xs = refl

macroSurface-scanOrder-lineMajor :
  ∀ (xs : DNA6x3) →
  MacroAdjacencySurface.scanOrder (macroSurface xs) ≡ lineMajor
macroSurface-scanOrder-lineMajor xs = refl

macroSurface-coupledAdjacency-true :
  ∀ (xs : DNA6x3) →
  MacroAdjacencySurface.coupledAdjacency (macroSurface xs) ≡ true
macroSurface-coupledAdjacency-true xs = refl

macroSurface-score-pair-swap-invariant :
  ∀ (x y : DNA3) →
  boolToNat (macroAdjacency2 x y) ≡ boolToNat (macroAdjacency2 y x)
macroSurface-score-pair-swap-invariant x y
  rewrite macroAdjacency2-sym x y = refl
