module DASHI.Reasoning.NullTriangleNativeH05ObserverExact where

-- Instantiate the ORIGINAL governed cube on the existing literal nine-trit
-- observer, with one retained refinement digit. This is a finite address
-- instance, not the intrinsic local field or a physical time operator.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)
open import Data.Vec using (Vec; []; _∷_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Reasoning.TrialecticObserverMatrix369Exact as O
import DASHI.Reasoning.Trialectic369HypervoxelUltrametricExact as V
import DASHI.Reasoning.NullTriangleOrderedUltrametricCubeExact as P
import DASHI.Reasoning.NullTriangleNineTritObserverWeldExact as W
import DASHI.Metric.AgreementUltrametric as U
import DASHI.Core.GovernedIndexedResidualCubeExact as H
import DASHI.Core.GovernedDiagramCore as G

Observer : Set
Observer = O.ObserverMatrix3 SSP.SSPTrit

to : Observer → Vec Trit 9
to = V.observerToTritVec9

from : Vec Trit 9 → Observer
from = V.tritVec9ToObserver

spectators : Vec Trit 9 → Vec Trit 7
spectators (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) =
  a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []

x9 y9 backX9 backY9 : Vec Trit 9 → Vec Trit 9
x9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) =
  W.attach (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) (P.stepX (x ∷ y ∷ []))
y9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) =
  W.attach (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) (P.stepY (x ∷ y ∷ []))
backX9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) =
  W.attach (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) (P.undoX (x ∷ y ∷ []))
backY9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) =
  W.attach (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ []) (P.undoY (x ∷ y ∷ []))

xy9 : ∀ v → y9 (x9 v) ≡ x9 (y9 v)
xy9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) = refl

keepX : ∀ v → spectators (x9 v) ≡ spectators v
keepX (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) = refl

keepY : ∀ v → spectators (y9 v) ≡ spectators v
keepY (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ []) = refl

inverseX9 : ∀ v → backX9 (x9 v) ≡ v
inverseX9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ [])
  rewrite P.prevNext x = refl

inverseY9 : ∀ v → backY9 (y9 v) ≡ v
inverseY9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ [])
  rewrite P.prevNext y = refl

reverseX9 : ∀ v → x9 (backX9 v) ≡ v
reverseX9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ [])
  rewrite P.nextPrev x = refl

reverseY9 : ∀ v → y9 (backY9 v) ≡ v
reverseY9 (a ∷ b ∷ c ∷ d ∷ e ∷ f ∷ g ∷ x ∷ y ∷ [])
  rewrite P.nextPrev y = refl

xO yO backXO backYO : Observer → Observer
xO o = from (x9 (to o))
yO o = from (y9 (to o))
backXO o = from (backX9 (to o))
backYO o = from (backY9 (to o))

vecX : ∀ o → to (xO o) ≡ x9 (to o)
vecX o = V.vecObserverRoundTrip (x9 (to o))

vecY : ∀ o → to (yO o) ≡ y9 (to o)
vecY o = V.vecObserverRoundTrip (y9 (to o))

xyO : ∀ o → yO (xO o) ≡ xO (yO o)
xyO o rewrite vecX o | vecY o = cong from (xy9 (to o))

inverseXO : ∀ o → backXO (xO o) ≡ o
inverseXO o rewrite vecX o | inverseX9 (to o) = V.observerVecRoundTrip o

inverseYO : ∀ o → backYO (yO o) ≡ o
inverseYO o rewrite vecY o | inverseY9 (to o) = V.observerVecRoundTrip o

reverseXO : ∀ o → xO (backXO o) ≡ o
reverseXO o rewrite V.vecObserverRoundTrip (backX9 (to o)) | reverseX9 (to o) =
  V.observerVecRoundTrip o

reverseYO : ∀ o → yO (backYO o) ≡ o
reverseYO o rewrite V.vecObserverRoundTrip (backY9 (to o)) | reverseY9 (to o) =
  V.observerVecRoundTrip o

x10 y10 backX10 backY10 : Vec Trit 10 → Vec Trit 10
x10 (t ∷ v) = t ∷ x9 v
y10 (t ∷ v) = t ∷ y9 v
backX10 (t ∷ v) = t ∷ backX9 v
backY10 (t ∷ v) = t ∷ backY9 v

prefix8 : Vec Trit 10 → Vec Trit 8
prefix8 (t ∷ v) = t ∷ spectators v

refine : Trit → Observer → Vec Trit 10
refine t o = t ∷ to o

recover : Vec Trit 10 → Observer
recover (t ∷ v) = from v

recoverRefine : ∀ t o → recover (refine t o) ≡ o
recoverRefine t o = V.observerVecRoundTrip o

-- Reverse is on the specified prefix image; no global inverse asserted.
refineRecover : ∀ t v → refine t (recover (t ∷ v)) ≡ t ∷ v
refineRecover t v = cong (t ∷_) (V.vecObserverRoundTrip v)

xy10 : ∀ v → y10 (x10 v) ≡ x10 (y10 v)
xy10 (t ∷ v) = cong (t ∷_) (xy9 v)

xz : ∀ t o → refine t (xO o) ≡ x10 (refine t o)
xz t o = cong (t ∷_) (vecX o)

yz : ∀ t o → refine t (yO o) ≡ y10 (refine t o)
yz t o = cong (t ∷_) (vecY o)

keepX10 : ∀ v → prefix8 (x10 v) ≡ prefix8 v
keepX10 (t ∷ v) = cong (t ∷_) (keepX v)

keepY10 : ∀ v → prefix8 (y10 v) ≡ prefix8 v
keepY10 (t ∷ v) = cong (t ∷_) (keepY v)

keepXO : ∀ o → spectators (to (xO o)) ≡ spectators (to o)
keepXO o = trans (cong spectators (vecX o)) (keepX (to o))

keepYO : ∀ o → spectators (to (yO o)) ≡ spectators (to o)
keepYO o = trans (cong spectators (vecY o)) (keepY (to o))

cube : Trit → H.Cube
cube t = record
  { A = Observer ; B = Observer ; C = Observer ; D = Observer
  ; E = Vec Trit 10 ; F = Vec Trit 10 ; H = Vec Trit 10 ; I = Vec Trit 10
  ; x00 = xO ; x10 = xO ; x01 = x10 ; x11 = x10
  ; y00 = yO ; y10 = yO ; y01 = y10 ; y11 = y10
  ; z00 = refine t ; z10 = refine t ; z01 = refine t ; z11 = refine t
  }

-- Residuals are actual spectator-retention equations, not unit placeholders.
faces : (t : Trit) → H.Faces (cube t)
faces t = record
  { Rxy0 = λ o → spectators (to (yO (xO o))) ≡ spectators (to o)
  ; Rxz0 = λ o → prefix8 (refine t (xO o)) ≡ t ∷ spectators (to o)
  ; Ryz0 = λ o → prefix8 (refine t (yO o)) ≡ t ∷ spectators (to o)
  ; Rxy1 = λ v → prefix8 (y10 (x10 v)) ≡ prefix8 v
  ; Rxz1 = λ o → prefix8 (refine t (xO o)) ≡ t ∷ spectators (to o)
  ; Ryz1 = λ o → prefix8 (refine t (yO o)) ≡ t ∷ spectators (to o)
  }

exact : (t : Trit) → H.ExactFaces (cube t) (faces t)
exact t = record
  { pxy0 = G.commutingSquareWitness xyO
  ; pxz0 = G.commutingSquareWitness (xz t)
  ; pyz0 = G.commutingSquareWitness (yz t)
  ; pxy1 = G.commutingSquareWitness xy10
  ; pxz1 = G.commutingSquareWitness (xz t)
  ; pyz1 = G.commutingSquareWitness (yz t)
  }

residual : (t : Trit) → H.ResidualFaces (cube t) (faces t)
residual t = record
  { rxy0 = G.residualSquareWitness (λ o →
      trans (keepYO (xO o)) (keepXO o))
  ; rxz0 = G.residualSquareWitness (λ o → cong (t ∷_) (keepXO o))
  ; ryz0 = G.residualSquareWitness (λ o → cong (t ∷_) (keepYO o))
  ; rxy1 = G.residualSquareWitness (λ v →
      trans (keepY10 (x10 v)) (keepX10 v))
  ; rxz1 = G.residualSquareWitness (λ o → cong (t ∷_) (keepXO o))
  ; ryz1 = G.residualSquareWitness (λ o → cong (t ∷_) (keepYO o))
  }

-- Do not identify the five indices with the trit or each other.
indexed : ∀ {History Time Depth Frob Version : Set} →
  (H.Index History Time Depth Frob Version → Trit) →
  H.IndexedCube (H.Index History Time Depth Frob Version)
indexed digit = record
  { cubeAt = λ k → cube (digit k)
  ; facesAt = λ k → faces (digit k)
  ; residualAt = λ k → residual (digit k)
  }

indexedExact : ∀ {History Time Depth Frob Version : Set}
  (digit : H.Index History Time Depth Frob Version → Trit)
  (k : H.Index History Time Depth Frob Version) →
  H.ExactFaces (H.cubeAt (indexed digit) k) (H.facesAt (indexed digit) k)
indexedExact digit k = exact (digit k)

endpointInverse : ∀ t o →
  backXO (backYO (recover (H.xyz (cube t) o))) ≡ o
endpointInverse t o
  rewrite recoverRefine t (yO (xO o))
        | inverseYO (xO o) | inverseXO o = refl

-- H05's existing endpoint-path theorems consume exact t directly.

refineDistance : ∀ t o p →
  U.dNat (refine t o) (refine t p) ≡ V.trialecticDistance o p
refineDistance t o p = P.prependIsometry t (to o) (to p)

inverseX10 : ∀ v → backX10 (x10 v) ≡ v
inverseX10 (t ∷ v) = cong (t ∷_) (inverseX9 v)

inverseY10 : ∀ v → backY10 (y10 v) ≡ v
inverseY10 (t ∷ v) = cong (t ∷_) (inverseY9 v)
