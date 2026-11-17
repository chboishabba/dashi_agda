module DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact where

-- F10-INC: replace aggregate-only face reconciliation by explicit IDs,
-- source and target incidence, oriented per-cell work and one-use receipts.
-- Reuse the original finite-volume LocalVolumeCell work theorem.
-- Physical E x H face quadrature and Maxwell spacetime Stokes remain OPEN.
-- Source attribution: classical oriented finite-volume incidence;
-- user-origin Smith/Filsinger solar-source/sink hypothesis is NOT proved.

open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeFaceIncidenceExact as Face
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

-- This is deliberately independent of source amplitudes and numeric
-- geometry. A zero-work face still requires exactly-once incidence.
sameID : Nat → Nat → Bool
sameID zero zero = true
sameID zero (suc _) = false
sameID (suc _) zero = false
sameID (suc x) (suc y) = sameID x y

chooseWork : Bool → Nat → Nat
chooseWork true w = w
chooseWork false _ = zero

markID : Nat → Nat → Nat
markID x y = chooseWork (sameID x y) (suc zero)

record IndexedCell : Set where
  constructor indexedCell
  field
    id : Nat
    budget : Face.LocalVolumeCell

record DirectedFace : Set where
  constructor directedFace
  field
    id source target work : Nat

sourceWork : IndexedCell → DirectedFace → Nat
sourceWork c f =
  chooseWork (sameID (IndexedCell.id c) (DirectedFace.source f))
    (DirectedFace.work f)

targetWork : IndexedCell → DirectedFace → Nat
targetWork c f =
  chooseWork (sameID (IndexedCell.id c) (DirectedFace.target f))
    (DirectedFace.work f)

sourceCount : IndexedCell → DirectedFace → Nat
sourceCount c f =
  markID (IndexedCell.id c) (DirectedFace.source f)

targetCount : IndexedCell → DirectedFace → Nat
targetCount c f =
  markID (IndexedCell.id c) (DirectedFace.target f)

-- All: evidence for exactly the elements actually in the list; unlike
-- a field indexed by arbitrary IDs, no proof is demanded for absent nodes.
data Every {A : Set} (P : A → Set) : List A → Set where
  everyNil : Every P []
  everyCons : ∀ {x xs} → P x → Every P xs → Every P (x ∷ xs)

everyMap :
  ∀ {A : Set} {P Q : A → Set} {xs : List A} →
  (∀ x → P x → Q x) → Every P xs → Every Q xs
everyMap fn everyNil = everyNil
everyMap fn (everyCons {x = x} p ps) =
  everyCons (fn x p) (everyMap fn ps)

-- Exactly-one incidence IMPLIES exactly one weighted-face contribution.
-- Even zero-valued faces remain required by the separate count receipts.
sumMarkedWeight :
  ∀ {A : Set} (xs : List A) (flag : A → Bool) (w : Nat) →
  Face.sumOf (λ x → chooseWork (flag x) w) xs
    ≡ (Face.sumOf (λ x → chooseWork (flag x) (suc zero)) xs) * w
sumMarkedWeight [] flag w = refl
sumMarkedWeight (x ∷ xs) flag w with flag x
... | true = cong (λ z → w + z) (sumMarkedWeight xs flag w)
... | false = sumMarkedWeight xs flag w

addZeroRight : (n : Nat) → n + zero ≡ n
addZeroRight zero = refl
addZeroRight (suc n) = cong suc (addZeroRight n)

sumMarkedOnce :
  ∀ {A : Set} (xs : List A) (flag : A → Bool) (w : Nat) →
  Face.sumOf (λ x → chooseWork (flag x) (suc zero)) xs
    ≡ suc zero →
  Face.sumOf (λ x → chooseWork (flag x) w) xs ≡ w
sumMarkedOnce xs flag w once =
  trans (sumMarkedWeight xs flag w)
    (trans (cong (λ n → n * w) once) (addZeroRight w))

sourceWorkFromCount :
  (cs : List IndexedCell) (f : DirectedFace) →
  Face.sumOf (λ c → sourceCount c f) cs ≡ suc zero →
  Face.sumOf (λ c → sourceWork c f) cs ≡ DirectedFace.work f
sourceWorkFromCount cs f p =
  sumMarkedOnce cs
    (λ c → sameID (IndexedCell.id c) (DirectedFace.source f))
    (DirectedFace.work f) p

targetWorkFromCount :
  (cs : List IndexedCell) (f : DirectedFace) →
  Face.sumOf (λ c → targetCount c f) cs ≡ suc zero →
  Face.sumOf (λ c → targetWork c f) cs ≡ DirectedFace.work f
targetWorkFromCount cs f p =
  sumMarkedOnce cs
    (λ c → sameID (IndexedCell.id c) (DirectedFace.target f))
    (DirectedFace.work f) p

sumEvery :
  ∀ {A : Set} {xs : List A} {f g : A → Nat} →
  Every (λ x → f x ≡ g x) xs →
  Face.sumOf f xs ≡ Face.sumOf g xs
sumEvery everyNil = refl
sumEvery {f = f} (everyCons {x = x} witness rest) =
  cong₂ _+_ witness (sumEvery rest)

sumZero : ∀ {A : Set} (xs : List A) →
  Face.sumOf (λ _ → zero) xs ≡ zero
sumZero [] = refl
sumZero (_ ∷ xs) = sumZero xs

-- A pure finite Fubini interchange: sum over cells of incident faces
-- equals sum over faces of all their actual incident cells.
sumSwap :
  ∀ {A B : Set} (xs : List A) (ys : List B) →
  (h : A → B → Nat) →
  Face.sumOf (λ x → Face.sumOf (h x) ys) xs
    ≡ Face.sumOf (λ y → Face.sumOf (λ x → h x y) xs) ys
sumSwap [] ys h = sym (sumZero ys)
sumSwap (x ∷ xs) ys h =
  trans
    (cong (λ z → Face.sumOf (h x) ys + z)
      (sumSwap xs ys h))
    (sym (Face.sumPairDistributes ys
      (h x) (λ y → Face.sumOf (λ x' → h x' y) xs)))

eraseCells : List IndexedCell → List Face.LocalVolumeCell
eraseCells [] = []
eraseCells (c ∷ cs) = IndexedCell.budget c ∷ eraseCells cs

eraseFaceWork : List DirectedFace → List Nat
eraseFaceWork [] = []
eraseFaceWork (f ∷ fs) = DirectedFace.work f ∷ eraseFaceWork fs

sumEraseIncoming :
  (cs : List IndexedCell) →
  Face.totalIntIn (eraseCells cs)
    ≡ Face.sumOf (λ c → Face.LocalVolumeCell.internalIncoming
      (IndexedCell.budget c)) cs
sumEraseIncoming [] = refl
sumEraseIncoming (c ∷ cs) =
  cong (λ n → Face.LocalVolumeCell.internalIncoming
    (IndexedCell.budget c) + n) (sumEraseIncoming cs)

sumEraseOutgoing :
  (cs : List IndexedCell) →
  Face.totalIntOut (eraseCells cs)
    ≡ Face.sumOf (λ c → Face.LocalVolumeCell.internalOutgoing
      (IndexedCell.budget c)) cs
sumEraseOutgoing [] = refl
sumEraseOutgoing (c ∷ cs) =
  cong (λ n → Face.LocalVolumeCell.internalOutgoing
    (IndexedCell.budget c) + n) (sumEraseOutgoing cs)

sumEraseFaces :
  (fs : List DirectedFace) →
  Face.sumOf DirectedFace.work fs
    ≡ Face.sumOf (λ w → w) (eraseFaceWork fs)
sumEraseFaces [] = refl
sumEraseFaces (f ∷ fs) =
  cong (λ n → DirectedFace.work f + n) (sumEraseFaces fs)

-- The former counterexample [4,0,3] for faces 0->1 (3),1->2 (4)
-- is NOT inhabitant evidence for the following record: each actual cell
-- must match its own endpoint-derived incident work, not merely its total.
record IndexedMesh : Set where
  constructor indexedMesh
  field
    cells : List IndexedCell
    faces : List DirectedFace

    -- IDs are unique even for zero-work faces, and no internal face
    -- starts and terminates at the same volume.
    uniqueCells : Every
      (λ c → Face.sumOf
        (λ x → markID (IndexedCell.id x) (IndexedCell.id c))
        cells ≡ suc zero) cells
    uniqueFaces : Every
      (λ f → Face.sumOf
        (λ x → markID (DirectedFace.id x) (DirectedFace.id f))
        faces ≡ suc zero) faces
    nonSelfFaces : Every
      (λ f → sameID (DirectedFace.source f)
        (DirectedFace.target f) ≡ false) faces

    -- Exact source/target assignment for every declared face. Counts
    -- remain necessary when the corresponding face work is ZERO.
    sourceExactlyOnce : Every
      (λ f → Face.sumOf (λ c → sourceCount c f) cells
        ≡ suc zero) faces
    targetExactlyOnce : Every
      (λ f → Face.sumOf (λ c → targetCount c f) cells
        ≡ suc zero) faces

    -- Oriented face-work receipts are derived from count=1 below.
    -- Per-CELL, not aggregate, matching of the physical local work
    -- budgets to the directed face endpoint contributions.
    outgoingIsSourceWork : Every
      (λ c → Face.LocalVolumeCell.internalOutgoing
        (IndexedCell.budget c)
        ≡ Face.sumOf (sourceWork c) faces) cells
    incomingIsTargetWork : Every
      (λ c → Face.LocalVolumeCell.internalIncoming
        (IndexedCell.budget c)
        ≡ Face.sumOf (targetWork c) faces) cells

sourceWorkReceipts :
  (m : IndexedMesh) →
  Every (λ f → Face.sumOf
    (λ c → sourceWork c f) (IndexedMesh.cells m)
      ≡ DirectedFace.work f) (IndexedMesh.faces m)
sourceWorkReceipts m =
  everyMap
    (λ face p → sourceWorkFromCount (IndexedMesh.cells m) face p)
    (IndexedMesh.sourceExactlyOnce m)

targetWorkReceipts :
  (m : IndexedMesh) →
  Every (λ f → Face.sumOf
    (λ c → targetWork c f) (IndexedMesh.cells m)
      ≡ DirectedFace.work f) (IndexedMesh.faces m)
targetWorkReceipts m =
  everyMap
    (λ face p → targetWorkFromCount (IndexedMesh.cells m) face p)
    (IndexedMesh.targetExactlyOnce m)

-- Existing aggregate evidence is now a DERIVED projection. Every face
-- contributes once at its unique source and once at its unique target.
outgoingFromIndexedFaces :
  (m : IndexedMesh) →
  Face.totalIntOut (eraseCells (IndexedMesh.cells m))
    ≡ Face.sumOf DirectedFace.work (IndexedMesh.faces m)
outgoingFromIndexedFaces m =
  trans (sumEraseOutgoing cs)
    (trans (sumEvery (IndexedMesh.outgoingIsSourceWork m))
      (trans (sumSwap cs fs sourceWork)
        (sumEvery (sourceWorkReceipts m))))
  where
    cs = IndexedMesh.cells m
    fs = IndexedMesh.faces m

incomingFromIndexedFaces :
  (m : IndexedMesh) →
  Face.totalIntIn (eraseCells (IndexedMesh.cells m))
    ≡ Face.sumOf DirectedFace.work (IndexedMesh.faces m)
incomingFromIndexedFaces m =
  trans (sumEraseIncoming cs)
    (trans (sumEvery (IndexedMesh.incomingIsTargetWork m))
      (trans (sumSwap cs fs targetWork)
        (sumEvery (targetWorkReceipts m))))
  where
    cs = IndexedMesh.cells m
    fs = IndexedMesh.faces m

-- NO second conservation law is posited. Import the original local
-- work proof and merely refine the mesh's physical incidence ownership.
asExistingMesh : IndexedMesh → Face.OrientedFaceMesh
asExistingMesh m =
  Face.orientedFaceMesh
    (eraseCells (IndexedMesh.cells m))
    (eraseFaceWork (IndexedMesh.faces m))
    (trans (incomingFromIndexedFaces m)
      (sumEraseFaces (IndexedMesh.faces m)))
    (trans (outgoingFromIndexedFaces m)
      (sumEraseFaces (IndexedMesh.faces m)))

indexedFaceExteriorEnergyBalance :
  (m : IndexedMesh) →
  Face.totalExtIn (eraseCells (IndexedMesh.cells m))
    + (Face.totalDrive (eraseCells (IndexedMesh.cells m))
      + Face.totalInitial (eraseCells (IndexedMesh.cells m)))
  ≡ Face.totalExtOut (eraseCells (IndexedMesh.cells m))
    + (Face.totalLoad (eraseCells (IndexedMesh.cells m))
      + (Face.totalLoss (eraseCells (IndexedMesh.cells m))
      + Face.totalFinal (eraseCells (IndexedMesh.cells m))))
indexedFaceExteriorEnergyBalance m =
  Face.finiteVolumeExteriorEnergyBalance (asExistingMesh m)

-- Transfer the existing exact upper bound to a mesh with checked
-- individual face IDs. Does not introduce a new arbitrary source cap.
indexedFaceUsefulLoadBound :
  (m : IndexedMesh) →
  Bound._≤_
    (Face.totalLoad (eraseCells (IndexedMesh.cells m)))
    (Face.totalExtIn (eraseCells (IndexedMesh.cells m))
      + (Face.totalDrive (eraseCells (IndexedMesh.cells m))
      + Face.totalInitial (eraseCells (IndexedMesh.cells m))))
indexedFaceUsefulLoadBound m =
  Face.finiteVolumeUsefulBelowAllSuppliedWork (asExistingMesh m)

indexedFaceSourceOffNoLoad :
  (m : IndexedMesh) →
  Face.totalExtIn (eraseCells (IndexedMesh.cells m)) ≡ zero →
  Face.totalDrive (eraseCells (IndexedMesh.cells m)) ≡ zero →
  Face.totalInitial (eraseCells (IndexedMesh.cells m)) ≡ zero →
  Face.totalLoad (eraseCells (IndexedMesh.cells m)) ≡ zero
indexedFaceSourceOffNoLoad m extOff driveOff storageOff =
  Face.finiteVolumeSourceFreeHasZeroLoad
    (asExistingMesh m) extOff driveOff storageOff

-- Nontrivial 2-cell physical adjacency: 0 -> 1, face ID 7, work 3.
-- Every actual per-cell / per-face identity is checked by reduction.
exampleIndexedMesh : IndexedMesh
exampleIndexedMesh =
  indexedMesh
    (indexedCell 0 (Face.localVolumeCell 8 0 0 0 3 3 1 1 0 refl)
      ∷ indexedCell 1 (Face.localVolumeCell 0 3 0 0 0 0 2 1 0 refl)
      ∷ [])
    (directedFace 7 0 1 3 ∷ [])
    (everyCons refl (everyCons refl everyNil))
    (everyCons refl everyNil)
    (everyCons refl everyNil)
    (everyCons refl everyNil)
    (everyCons refl everyNil)
    (everyCons refl (everyCons refl everyNil))
    (everyCons refl (everyCons refl everyNil))

exampleIndexedMeshConserves :
  Face.totalExtIn (eraseCells (IndexedMesh.cells exampleIndexedMesh))
    + (Face.totalDrive (eraseCells (IndexedMesh.cells exampleIndexedMesh))
      + Face.totalInitial (eraseCells (IndexedMesh.cells exampleIndexedMesh)))
  ≡ Face.totalExtOut (eraseCells (IndexedMesh.cells exampleIndexedMesh))
    + (Face.totalLoad (eraseCells (IndexedMesh.cells exampleIndexedMesh))
      + (Face.totalLoss (eraseCells (IndexedMesh.cells exampleIndexedMesh))
      + Face.totalFinal (eraseCells (IndexedMesh.cells exampleIndexedMesh))))
exampleIndexedMeshConserves =
  indexedFaceExteriorEnergyBalance exampleIndexedMesh

-- F10 field integration and F13 source-to-port admission remain OPEN.
-- Real signed flux orientation is NOT obtained from nonnegative Nat work;
-- real measured E,H,J and true Poynting face quadrature are separate.
