module DASHI.Physics.Motors.SmithFilsingerLocalCausalADEFrameExact where

-- Source-first F13 finite LOCAL support theorem, reusing strict
-- decidable coordinate IDs from IndexedFaceIncidenceExact.
-- Each primitive update changes only its two named coordinates.
-- Unmentioned coordinates are unchanged after ANY finite list of
-- local stages, independent of arbitrary noncommuting update order.
--
-- This is a structural frame theorem; not a proved real Maxwell light
-- cone, not a Cayley energy theorem, and not a calibrated atmosphere.

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Motors.SmithFilsingerIndexedFaceIncidenceExact as Indexed

record LocalPrimitive (A : Set) : Set where
  constructor localPrimitive
  field
    firstID secondID : Nat
    firstValue secondValue : A → A → A

State : Set → Set
State A = Nat → A

-- This is the coordinate projection of a two-index update.
-- The actual Cayley solver, coefficients and source signed work
-- are independent mathematical owners and are not reasserted here.
applyPrimitive :
  ∀ {A : Set} → LocalPrimitive A → State A → State A
applyPrimitive p s k with
    Indexed.sameID k (LocalPrimitive.firstID p)
  | Indexed.sameID k (LocalPrimitive.secondID p)
... | true | _ =
  LocalPrimitive.firstValue p
    (s (LocalPrimitive.firstID p))
    (s (LocalPrimitive.secondID p))
... | false | true =
  LocalPrimitive.secondValue p
    (s (LocalPrimitive.firstID p))
    (s (LocalPrimitive.secondID p))
... | false | false = s k

-- Proof that a coordinate untouched by this exact stage is unchanged.
outsidePrimitive :
  ∀ {A : Set} (p : LocalPrimitive A) (s : State A) (k : Nat) →
  Indexed.sameID k (LocalPrimitive.firstID p) ≡ false →
  Indexed.sameID k (LocalPrimitive.secondID p) ≡ false →
  applyPrimitive p s k ≡ s k
outsidePrimitive p s k firstOutside secondOutside
  rewrite firstOutside | secondOutside = refl

-- An independent, data-carrying receipt for EACH actual stage in the
-- list, not a vacuous claim about only one arbitrarily chosen stage.
data OutsideEvery {A : Set} (k : Nat) :
  List (LocalPrimitive A) → Set where
  outsideNil : OutsideEvery k []
  outsideCons :
    ∀ {p ps} →
    Indexed.sameID k (LocalPrimitive.firstID p) ≡ false →
    Indexed.sameID k (LocalPrimitive.secondID p) ≡ false →
    OutsideEvery k ps →
    OutsideEvery k (p ∷ ps)

applyStages :
  ∀ {A : Set} → List (LocalPrimitive A) → State A → State A
applyStages [] s = s
applyStages (p ∷ ps) s =
  applyStages ps (applyPrimitive p s)

-- General all-N finite frame: a coordinate never incident to the
-- selected local update sequence cannot receive a fabricated signal.
neverTouchedRetainsOriginal :
  ∀ {A : Set} (ps : List (LocalPrimitive A))
  (s : State A) (k : Nat) →
  OutsideEvery k ps →
  applyStages ps s k ≡ s k
neverTouchedRetainsOriginal [] s k outsideNil = refl
neverTouchedRetainsOriginal (p ∷ ps) s k
  (outsideCons firstOutside secondOutside rest) =
  trans
    (neverTouchedRetainsOriginal ps (applyPrimitive p s) k rest)
    (outsidePrimitive p s k firstOutside secondOutside)

-- IMPORTANT: this does not claim that every coordinate outside a
-- *dynamic* reachability set is untouched. That stronger graph-cone
-- induction is separately exercised by local SymPy stage receipts.
-- Physical speed bound, original-source replenishment and 3D Maxwell
-- retarded dyadic still require independent proof/evidence.
