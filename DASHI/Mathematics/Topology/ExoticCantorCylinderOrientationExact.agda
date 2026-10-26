module DASHI.Mathematics.Topology.ExoticCantorCylinderOrientationExact where

------------------------------------------------------------------------
-- EXACT SAME-OBJECT WARNING: FINITE WORDS VS CHRONOLOGICAL CYLINDERS
--
-- EXISTING OWNER:
-- DASHI.Foundations.CantorProjectiveCylinderMeasureExact (unmodified).
-- Its leftChild (cylinder prefix) = cylinder (false :: prefix).
-- This is correct for an ADDRESS STACK stored in reverse order, but
-- does NOT refine a chronological first-n-digits event interpreted
-- by matching positions 0,1,... of a binary stream.
--
-- Our geometric Cantor frontier uses parent p -> children p0,p1
-- by APPENDING a digit. The source's PREPEND mass formula is valid
-- because mass depends only on word length; it does not establish
-- chronological clopen-event inclusion on the very same carrier.
--
-- Here we reuse existing Cantor.BitStream and Cantor.Cylinder,
-- introduce the explicitly declared chronological interpretation,
-- PROVE append-child event inclusion for ALL words/streams, and
-- exhibit an explicit same-carrier counterexample to prepend-child
-- inclusion. No new Borel measure or Richards-end homeomorphism
-- is claimed. These are source-written, kernel-check required.
--
-- Source mathematics: elementary binary sequence product topology.
-- Original infinite-surface end classification: Richards (1963).
-- DASHI owner retains original Cantor cylinder mass implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (_++_)
open import Data.Product using (_×_; _,_)
open import Data.Product.Base using (proj₁)
open import Data.Empty using (⊥)

import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Cantor

-- A prefix is interpreted in chronological stream order: the head
-- matches stream position n and the tail begins at position n+1.
MatchesAt : Nat → List Bool → Cantor.BitStream → Set
MatchesAt n [] stream = ⊤
MatchesAt n (bit ∷ remaining) stream =
  (stream n ≡ bit) × MatchesAt (suc n) remaining stream

Matches : Cantor.Cylinder → Cantor.BitStream → Set
Matches event stream = MatchesAt zero (Cantor.prefix event) stream

-- Correct children in the standard product-of-streams topology.
appendChild : Bool → Cantor.Cylinder → Cantor.Cylinder
appendChild bit (Cantor.cylinder prefix) =
  Cantor.cylinder (prefix ++ (bit ∷ []))

appendLeft appendRight : Cantor.Cylinder → Cantor.Cylinder
appendLeft = appendChild false
appendRight = appendChild true

-- No finite word restriction, no abstract 'refines' assumption.
-- This establishes actual inclusion of interpreted cylinder EVENTS.
appendChildRefinesAt :
  (n : Nat) (prefix : List Bool) (bit : Bool)
  (stream : Cantor.BitStream) →
  MatchesAt n (prefix ++ (bit ∷ [])) stream →
  MatchesAt n prefix stream
appendChildRefinesAt n [] bit stream evidence = tt
appendChildRefinesAt n (b ∷ rest) bit stream (head , tail) =
  head , appendChildRefinesAt (suc n) rest bit stream tail

appendChildRefines :
  (event : Cantor.Cylinder) (bit : Bool)
  (stream : Cantor.BitStream) →
  Matches (appendChild bit event) stream →
  Matches event stream
appendChildRefines (Cantor.cylinder prefix) bit stream =
  appendChildRefinesAt zero prefix bit stream

appendLeftRefines :
  (event : Cantor.Cylinder) (stream : Cantor.BitStream) →
  Matches (appendLeft event) stream → Matches event stream
appendLeftRefines event stream =
  appendChildRefines event false stream

appendRightRefines :
  (event : Cantor.Cylinder) (stream : Cantor.BitStream) →
  Matches (appendRight event) stream → Matches event stream
appendRightRefines event stream =
  appendChildRefines event true stream

-- Counterexample to the silently assumed chronological meaning of
-- the existing PREPEND operation. Parent requires stream(0)=true;
-- its old leftChild instead requires stream(0)=false, stream(1)=true.
sampleParent : Cantor.Cylinder
sampleParent = Cantor.cylinder (true ∷ [])

sampleStream : Cantor.BitStream
sampleStream zero = false
sampleStream (suc zero) = true
sampleStream (suc (suc n)) = false

oldPrependChildMembership :
  Matches (Cantor.leftChild sampleParent) sampleStream
oldPrependChildMembership = refl , (refl , tt)

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

oldPrependIsNotChronologicalRefinement :
  ((stream : Cantor.BitStream) →
   Matches (Cantor.leftChild sampleParent) stream →
   Matches sampleParent stream) → ⊥
oldPrependIsNotChronologicalRefinement allIncluded =
  falseNotTrue (proj₁ (allIncluded sampleStream oldPrependChildMembership))

-- This repairs only the EVENT-ORIENTATION relation. The source's
-- dyadic cylinderMass identities remain attributed to their owner;
-- no incorrect claim of measure preservation or 2-adic / 3-adic
-- group equivalence is introduced.
