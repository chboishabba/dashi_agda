module DASHI.Foundations.Base369PrefixUltrametricExact where

------------------------------------------------------------------------
-- MATHEMATICAL BACKGROUND
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Graduate Texts in
-- Mathematics 7, Springer. DOI: 10.1007/978-1-4684-9884-4.
--
-- DASHI CONTRIBUTION
--
-- Finite balanced-ternary addresses carry the exact prefix relation underlying
-- the usual 3-adic-style ultrametric intuition.  Rather than pretending that a
-- real-valued 3^{-k} metric has already been constructed, this module proves
-- the stronger discrete threshold law directly: agreement to depth k is
-- reflexive, symmetric, and transitive.  Hence every fixed-depth prefix ball is
-- an equivalence class, which is the finite non-Archimedean geometry used by
-- dynamic branch quotienting.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import Base369 using (TriTruth)
open import DASHI.Foundations.Base369AddressSymmetryAndBranchGeometryExact using
  ( TritPath
  ; []
  ; _∷_
  )

------------------------------------------------------------------------
-- PrefixAgree k x y means x and y have the same first k trits.  The type makes
-- it impossible to construct a witness deeper than the available path.
------------------------------------------------------------------------

data PrefixAgree :
  {n : Nat} →
  Nat →
  TritPath n →
  TritPath n →
  Set where
  prefixZero :
    {n : Nat} →
    {left right : TritPath n} →
    PrefixAgree zero left right

  prefixSuc :
    {n k : Nat} →
    {head : TriTruth} →
    {left right : TritPath n} →
    PrefixAgree k left right →
    PrefixAgree (suc k) (head ∷ left) (head ∷ right)

------------------------------------------------------------------------
-- Full-depth reflexivity.
------------------------------------------------------------------------

fullPrefixReflexive :
  {n : Nat} →
  (path : TritPath n) →
  PrefixAgree n path path
fullPrefixReflexive [] = prefixZero
fullPrefixReflexive (head ∷ tail) =
  prefixSuc (fullPrefixReflexive tail)

------------------------------------------------------------------------
-- Symmetry and the finite ultrametric threshold law.
------------------------------------------------------------------------

prefixSymmetric :
  {n k : Nat} →
  {left right : TritPath n} →
  PrefixAgree k left right →
  PrefixAgree k right left
prefixSymmetric prefixZero = prefixZero
prefixSymmetric (prefixSuc witness) =
  prefixSuc (prefixSymmetric witness)

prefixUltrametricThreshold :
  {n k : Nat} →
  {left middle right : TritPath n} →
  PrefixAgree k left middle →
  PrefixAgree k middle right →
  PrefixAgree k left right
prefixUltrametricThreshold prefixZero prefixZero = prefixZero
prefixUltrametricThreshold (prefixSuc leftMiddle) (prefixSuc middleRight) =
  prefixSuc
    (prefixUltrametricThreshold leftMiddle middleRight)

------------------------------------------------------------------------
-- If two paths agree at depth k+1 they also agree at depth k.  This supplies
-- the nested-ball filtration explicitly.
------------------------------------------------------------------------

weakenPrefixOne :
  {n k : Nat} →
  {left right : TritPath n} →
  PrefixAgree (suc k) left right →
  PrefixAgree k left right
weakenPrefixOne {k = zero} witness = prefixZero
weakenPrefixOne {k = suc k} (prefixSuc witness) =
  prefixSuc (weakenPrefixOne witness)

------------------------------------------------------------------------
-- Equal complete paths inherit agreement at every representable prefix depth
-- by transporting the full-depth witness through ordinary equality.
------------------------------------------------------------------------

prefixTransportAlongEquality :
  {n : Nat} →
  {left right : TritPath n} →
  left ≡ right →
  PrefixAgree n left right
prefixTransportAlongEquality {left = left} refl =
  fullPrefixReflexive left
