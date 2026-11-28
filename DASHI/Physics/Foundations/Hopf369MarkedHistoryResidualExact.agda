module DASHI.Physics.Foundations.Hopf369MarkedHistoryResidualExact where

-- BR286: native source-specific affine history attachment on the original
-- marked chart. Not an autonomous flow or authenticated numerical snapshot.
-- Source-written; kernel acceptance outstanding.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_; _-_)
import Data.Rational.Tactic.RingSolver as Ring
import DASHI.Core.GovernedIndexedResidualCubeExact as C
import DASHI.Core.GovernedDiagramCore as G
import DASHI.Physics.Foundations.Hopf369MarkedTidalCubeExact as M

record Step : Set where
  field
    mark : C.Index Nat Nat Nat Nat Nat
    centre evenIncrement oddIncrement : ℚ
open Step public

advance : Step → M.Marked → M.Marked
advance s (M.marked q e) = M.marked (q + evenIncrement s) (e + oddIncrement s)

advanceSplit : Step → M.Split → M.Split
advanceSplit s (M.split q e) = M.split (q + evenIncrement s) (e + oddIncrement s)

cube : Step → C.Cube
cube s = record
  { A = M.Marked ; B = M.Split ; C = M.Marked ; D = M.Split
  ; E = M.Marked ; F = M.Split ; H = M.Marked ; I = M.Split
  ; x00 = M.observe ; x10 = M.observe ; x01 = M.observe ; x11 = M.observe
  ; y00 = M.reflect (centre s) ; y10 = M.reflectSplit (centre s)
  ; y01 = M.reflect (centre s) ; y11 = M.reflectSplit (centre s)
  ; z00 = advance s ; z10 = advanceSplit s
  ; z01 = advance s ; z11 = advanceSplit s
  }

-- Keep the even component and signed odd path difference, not just a norm.
record MarkedResidual (s : Step) (a : M.Marked) : Set where
  field
    evenAgreement :
      M.evenScale (advance s (M.reflect (centre s) a)) ≡
      M.evenScale (M.reflect (centre s) (advance s a))
    oddDifference :
      M.signedAmplitude (advance s (M.reflect (centre s) a)) -
      M.signedAmplitude (M.reflect (centre s) (advance s a)) ≡
      oddIncrement s + oddIncrement s

record SplitResidual (s : Step) (a : M.Split) : Set where
  field
    evenAgreement :
      M.coarse (advanceSplit s (M.reflectSplit (centre s) a)) ≡
      M.coarse (M.reflectSplit (centre s) (advanceSplit s a))
    oddDifference :
      M.residual (advanceSplit s (M.reflectSplit (centre s) a)) -
      M.residual (M.reflectSplit (centre s) (advanceSplit s a)) ≡
      oddIncrement s + oddIncrement s

faces : (s : Step) → C.Faces (cube s)
faces s = record
  { Rxy0 = λ a → M.reflectSplit (centre s) (M.observe a) ≡ M.observe (M.reflect (centre s) a)
  ; Rxz0 = λ a → advanceSplit s (M.observe a) ≡ M.observe (advance s a)
  ; Ryz0 = MarkedResidual s
  ; Rxy1 = λ a → M.reflectSplit (centre s) (M.observe a) ≡ M.observe (M.reflect (centre s) a)
  ; Rxz1 = λ a → advanceSplit s (M.observe a) ≡ M.observe (advance s a)
  ; Ryz1 = SplitResidual s
  }

markedWitness : (s : Step) (a : M.Marked) → MarkedResidual s a
markedWitness s (M.marked q e) = record
  { evenAgreement = refl
  ; oddDifference = Ring.solve-∀ (centre s) e (oddIncrement s)
  }

splitWitness : (s : Step) (a : M.Split) → SplitResidual s a
splitWitness s (M.split q e) = record
  { evenAgreement = refl
  ; oddDifference = Ring.solve-∀ (centre s) e (oddIncrement s)
  }

residuals : (s : Step) → C.ResidualFaces (cube s) (faces s)
residuals s = record
  { rxy0 = G.residualSquareWitness (λ { (M.marked q e) → refl })
  ; rxz0 = G.residualSquareWitness (λ { (M.marked q e) → refl })
  ; ryz0 = G.residualSquareWitness (markedWitness s)
  ; rxy1 = G.residualSquareWitness (λ { (M.marked q e) → refl })
  ; rxz1 = G.residualSquareWitness (λ { (M.marked q e) → refl })
  ; ryz1 = G.residualSquareWitness (splitWitness s)
  }

indexed : C.IndexedCube Step
indexed = record { cubeAt = cube ; facesAt = faces ; residualAt = residuals }
