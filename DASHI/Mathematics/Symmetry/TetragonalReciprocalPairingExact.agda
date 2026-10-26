module DASHI.Mathematics.Symmetry.TetragonalReciprocalPairingExact where

-- Abstract exact bilinear pairing with involutive scalar negation.
-- The classical integral D4h action preserves the pairing; no
-- particular band structure, metric scale or specimen is assumed.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)
open import Agda.Builtin.Bool using (Bool; true; false)
import DASHI.Mathematics.Symmetry.TetragonalD4hNormalFormExact as D
import DASHI.Mathematics.Symmetry.TetragonalIntegralLatticeActionExact as T

record PairingLaws (A : Set) : Set₁ where
  field
    signed : T.SignedCarrier A
    dot : T.Triple A → T.Triple A → A
    rotateInvariant : (x k : T.Triple A) →
      dot (T.R signed x) (T.R signed k) ≡ dot x k
    verticalInvariant : (x k : T.Triple A) →
      dot (T.V signed x) (T.V signed k) ≡ dot x k
    horizontalInvariant : (x k : T.Triple A) →
      dot (T.H signed x) (T.H signed k) ≡ dot x k
open PairingLaws public

quarterInvariant :
  ∀ {A} (P : PairingLaws A)
    (q : D.Quarter)
    (x k : T.Triple A) →
  dot P (T.quarter (signed P) q x) (T.quarter (signed P) q k) ≡ dot P x k
quarterInvariant P D.q0 x k = refl
quarterInvariant P D.q1 x k =
  rotateInvariant P x k
quarterInvariant P D.q2 x k =
  trans (rotateInvariant P (T.R (signed P) x) (T.R (signed P) k))
        (rotateInvariant P x k)
quarterInvariant P D.q3 x k =
  trans (rotateInvariant P (T.R (signed P) (T.R (signed P) x))
                             (T.R (signed P) (T.R (signed P) k)))
        (quarterInvariant P D.q2 x k)

-- All sixteen group elements are products of three isometries.
fullPairingInvariant :
  ∀ {A} (P : PairingLaws A)
    (g : D.D4h)
    (x k : T.Triple A) →
  dot P (T.act (signed P) g x) (T.act (signed P) g k) ≡ dot P x k
fullPairingInvariant {A} P
  (D.element q b c) x k =
  trans (quarterInvariant P q
           (T.vertical (signed P) b (T.horizontal (signed P) c x))
           (T.vertical (signed P) b (T.horizontal (signed P) c k)))
        (trans (verticalCase b (T.horizontal (signed P) c x)
                                (T.horizontal (signed P) c k))
               (horizontalCase c x k))
  where
  verticalCase : (b : Bool) (u v : T.Triple A) →
    dot P (T.vertical (signed P) b u) (T.vertical (signed P) b v) ≡ dot P u v
  verticalCase false u v = refl
  verticalCase true u v = verticalInvariant P u v
  horizontalCase : (c : Bool) (u v : T.Triple A) →
    dot P (T.horizontal (signed P) c u) (T.horizontal (signed P) c v) ≡ dot P u v
  horizontalCase false u v = refl
  horizontalCase true u v = horizontalInvariant P u v
