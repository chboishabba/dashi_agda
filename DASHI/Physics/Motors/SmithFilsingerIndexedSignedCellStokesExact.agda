module DASHI.Physics.Motors.SmithFilsingerIndexedSignedCellStokesExact where

-- Strict face-ID incidence + field-valued discrete oriented Stokes sum.
-- ALL-N mathematical cancellation of internal signed field flux over
-- arbitrary branching/cyclic finite mesh, deriving work from exact
-- source/target count evidence, not an asserted aggregate flux equality.
--
-- It is NOT yet a verified integration of the KSW668 pointwise Maxwell
-- PDE or an SI Yee discrete Poynting theorem; field face quadrature,
-- Maxwell regularity, boundary source and material work remain open.

open import Agda.Primitive using (Level)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact as Face
import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed
import DASHI.Physics.Motors.SmithFilsingerSignedIndexedFaceFluxExact as Signed

mark : Bool → Nat
mark true = suc zero
mark false = zero

chooseField :
  ∀ {r} (F : C3.RealField r) →
  Bool → C3.Carrier F → C3.Carrier F
chooseField F true w = w
chooseField F false w = C3.zero F

-- The mark-count criterion is a genuine exactly-one incidence condition:
-- if a face has a zero signed flux it still must have a source and target.
markedZeroImpliesFieldZero :
  ∀ {r} {A : Set} (F : C3.RealField r)
  (xs : List A) (flag : A → Bool) (w : C3.Carrier F) →
  Face.sumOf (λ x → mark (flag x)) xs ≡ zero →
  Signed.sumField F (λ x → chooseField F (flag x) w) xs
    ≡ C3.zero F
markedZeroImpliesFieldZero F [] flag w p = refl
markedZeroImpliesFieldZero F (x ∷ xs) flag w p with flag x
... | true = impossible
  where
    impossible : Signed.sumField F
      (λ x' → chooseField F (flag x') w) (x ∷ xs)
      ≡ C3.zero F
    impossible with p
    ... | ()
... | false =
  trans
    (C3.addZeroLeft F
      (Signed.sumField F
        (λ x' → chooseField F (flag x') w) xs))
    (markedZeroImpliesFieldZero F xs flag w p)

sucInject : ∀ {a b : Nat} → suc a ≡ suc b → a ≡ b
sucInject refl = refl

markedOnceField :
  ∀ {r} {A : Set} (F : C3.RealField r)
  (xs : List A) (flag : A → Bool) (w : C3.Carrier F) →
  Face.sumOf (λ x → mark (flag x)) xs ≡ suc zero →
  Signed.sumField F (λ x → chooseField F (flag x) w) xs ≡ w
markedOnceField F [] flag w ()
markedOnceField F (x ∷ xs) flag w p with flag x
... | true =
  trans
    (cong (C3.add F w)
      (markedZeroImpliesFieldZero F xs flag w (sucInject p)))
    (Algebra.realAddZeroRight F w)
... | false =
  trans
    (C3.addZeroLeft F
      (Signed.sumField F
        (λ x' → chooseField F (flag x') w) xs))
    (markedOnceField F xs flag w p)

sumFieldZero :
  ∀ {r} {A : Set} (F : C3.RealField r) (xs : List A) →
  Signed.sumField F (λ _ → C3.zero F) xs ≡ C3.zero F
sumFieldZero F [] = refl
sumFieldZero F (x ∷ xs) =
  trans
    (cong (C3.add F (C3.zero F)) (sumFieldZero F xs))
    (C3.addZeroLeft F (C3.zero F))

sumFieldPairDistributes :
  ∀ {r} {A : Set} (F : C3.RealField r)
  (xs : List A) (p q : A → C3.Carrier F) →
  Signed.sumField F
    (λ x → C3.add F (p x) (q x)) xs
  ≡ C3.add F
      (Signed.sumField F p xs)
      (Signed.sumField F q xs)
sumFieldPairDistributes F [] p q =
  sym (C3.addZeroLeft F (C3.zero F))
sumFieldPairDistributes F (x ∷ xs) p q =
  trans
    (cong (C3.add F (C3.add F (p x) (q x)))
      (sumFieldPairDistributes F xs p q))
    (R.solve 4
      (λ a b c d →
        ((a R.⊕ b) R.⊕ (c R.⊕ d))
          R.⊜ ((a R.⊕ c) R.⊕ (b R.⊕ d)))
      refl (p x) (q x)
      (Signed.sumField F p xs) (Signed.sumField F q xs))
  where module R = Algebra.Solver F

sumFieldSwap :
  ∀ {r} {A B : Set} (F : C3.RealField r)
  (xs : List A) (ys : List B)
  (h : A → B → C3.Carrier F) →
  Signed.sumField F
    (λ x → Signed.sumField F (h x) ys) xs
  ≡ Signed.sumField F
    (λ y → Signed.sumField F (λ x → h x y) xs) ys
sumFieldSwap F [] ys h = sym (sumFieldZero F ys)
sumFieldSwap F (x ∷ xs) ys h =
  trans
    (cong (C3.add F (Signed.sumField F (h x) ys))
      (sumFieldSwap F xs ys h))
    (sym (sumFieldPairDistributes F ys
      (h x)
      (λ y → Signed.sumField F (λ x' → h x' y) xs)))

sumFieldEvery :
  ∀ {r} {A : Set} {F : C3.RealField r}
  {xs : List A} {p q : A → C3.Carrier F} →
  Indexed.Every (λ x → p x ≡ q x) xs →
  Signed.sumField F p xs ≡ Signed.sumField F q xs
sumFieldEvery Indexed.everyNil = refl
sumFieldEvery {F = F} (Indexed.everyCons witness rest) =
  cong₂ (C3.add F) witness (sumFieldEvery rest)

everyZip :
  ∀ {A : Set} {P Q R : A → Set} {xs : List A} →
  (∀ x → P x → Q x → R x) →
  Indexed.Every P xs → Indexed.Every Q xs → Indexed.Every R xs
everyZip fn Indexed.everyNil Indexed.everyNil = Indexed.everyNil
everyZip fn (Indexed.everyCons {x = x} p ps)
  (Indexed.everyCons q qs) =
  Indexed.everyCons (fn x p q) (everyZip fn ps qs)

sourceSelected :
  ∀ {r} (F : C3.RealField r)
  (flux : Indexed.DirectedFace → C3.Carrier F) →
  Indexed.IndexedCell → Indexed.DirectedFace → C3.Carrier F
sourceSelected F flux c face =
  chooseField F
    (Indexed.sameID (Indexed.IndexedCell.id c)
      (Indexed.DirectedFace.source face))
    (flux face)

targetSelected :
  ∀ {r} (F : C3.RealField r)
  (flux : Indexed.DirectedFace → C3.Carrier F) →
  Indexed.IndexedCell → Indexed.DirectedFace → C3.Carrier F
targetSelected F flux c face =
  chooseField F
    (Indexed.sameID (Indexed.IndexedCell.id c)
      (Indexed.DirectedFace.target face))
    (C3.negate F (flux face))

perCellSignedWork :
  ∀ {r} (F : C3.RealField r)
  (flux : Indexed.DirectedFace → C3.Carrier F)
  (faces : List Indexed.DirectedFace) →
  Indexed.IndexedCell → C3.Carrier F
perCellSignedWork F flux faces cell =
  Signed.sumField F
    (λ face → C3.add F
      (sourceSelected F flux cell face)
      (targetSelected F flux cell face))
    faces

-- The two oriented incidences of EACH FACE cancel, rather than relying
-- on arbitrary matching of total source and destination flux magnitudes.
perFaceSignedZero :
  ∀ {r} (F : C3.RealField r)
  (cells : List Indexed.IndexedCell)
  (flux : Indexed.DirectedFace → C3.Carrier F)
  (face : Indexed.DirectedFace) →
  Face.sumOf (λ c → Indexed.sourceCount c face) cells ≡ suc zero →
  Face.sumOf (λ c → Indexed.targetCount c face) cells ≡ suc zero →
  Signed.sumField F
    (λ cell → C3.add F
      (sourceSelected F flux cell face)
      (targetSelected F flux cell face)) cells
    ≡ C3.zero F
perFaceSignedZero F cs flux face sourceOnce targetOnce =
  trans
    (sumFieldPairDistributes F cs
      (λ c → sourceSelected F flux c face)
      (λ c → targetSelected F flux c face))
    (trans
      (cong₂ (C3.add F)
        (markedOnceField F cs
          (λ c → Indexed.sameID (Indexed.IndexedCell.id c)
            (Indexed.DirectedFace.source face))
          (flux face) sourceOnce)
        (markedOnceField F cs
          (λ c → Indexed.sameID (Indexed.IndexedCell.id c)
            (Indexed.DirectedFace.target face))
          (C3.negate F (flux face)) targetOnce))
      (Algebra.realAddInverseRight F (flux face)))

perFaceZeros :
  ∀ {r} (F : C3.RealField r)
  (mesh : Indexed.IndexedMesh)
  (flux : Indexed.DirectedFace → C3.Carrier F) →
  Indexed.Every
    (λ face → Signed.sumField F
      (λ cell → C3.add F
        (sourceSelected F flux cell face)
        (targetSelected F flux cell face))
      (Indexed.IndexedMesh.cells mesh)
      ≡ C3.zero F)
    (Indexed.IndexedMesh.faces mesh)
perFaceZeros F mesh flux =
  everyZip
    (λ f sourceOnce targetOnce →
      perFaceSignedZero F (Indexed.IndexedMesh.cells mesh)
        flux f sourceOnce targetOnce)
    (Indexed.IndexedMesh.sourceExactlyOnce mesh)
    (Indexed.IndexedMesh.targetExactlyOnce mesh)

-- Strong F10-INC/finite-Stokes theorem: SUM OF EACH CELL'S ACTUAL
-- directed field-valued face-work over ANY strict indexed mesh = 0.
-- This uses a genuine all-N sum interchange, per-face exact source
-- and target ID incidence, and opposite signed orientation.
allIndexedInternalSignedFluxCancels :
  ∀ {r} (F : C3.RealField r)
  (mesh : Indexed.IndexedMesh)
  (flux : Indexed.DirectedFace → C3.Carrier F) →
  Signed.sumField F
    (perCellSignedWork F flux (Indexed.IndexedMesh.faces mesh))
    (Indexed.IndexedMesh.cells mesh)
    ≡ C3.zero F
allIndexedInternalSignedFluxCancels F mesh flux =
  trans
    (sumFieldSwap F
      (Indexed.IndexedMesh.cells mesh)
      (Indexed.IndexedMesh.faces mesh)
      (λ cell face → C3.add F
        (sourceSelected F flux cell face)
        (targetSelected F flux cell face)))
    (trans
      (sumFieldEvery (perFaceZeros F mesh flux))
      (sumFieldZero F (Indexed.IndexedMesh.faces mesh)))

-- True F10-PDE/STOKES still OPEN: show cell flux is the exact spacetime
-- integral of Maxwell E×H over actual oriented geometry, with material
-- and source/receiver work. This proves ONLY finite face algebra.
