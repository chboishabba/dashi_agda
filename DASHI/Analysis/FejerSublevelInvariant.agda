module DASHI.Analysis.FejerSublevelInvariant where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Energy.Core as EC
import DASHI.Energy.Fejer as FE

------------------------------------------------------------------------
-- Generic sublevel-set invariance from Fejer monotonicity.
--
-- A predicate S is represented by a distance sublevel around a target.  Fejer
-- monotonicity then makes S forward invariant, and induction gives invariance
-- under every finite iterate.
------------------------------------------------------------------------

record FejerSublevelInvariant
    {x e p : Level}
    {X : Set x}
    {Energy : Set e}
    (ES : EC.EnergySpace X Energy)
    (transition : X → X)
    (target : X)
    (S : X → Set p)
    (radius : Energy)
    : Set (lsuc (x ⊔ e ⊔ p)) where
  field
    fejerPoint :
      FE.FejerPoint ES transition target

    memberToSublevel :
      (x : X) →
      S x →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (FE.FejerPoint.d fejerPoint x target)
        radius

    sublevelToMember :
      (x : X) →
      EC.Preorder._≤_ (EC.EnergySpace.P ES)
        (FE.FejerPoint.d fejerPoint x target)
        radius →
      S x

open FejerSublevelInvariant public

fejerPreservesSublevel :
  ∀ {x e p X Energy ES transition target S radius} →
  (F : FejerSublevelInvariant
    {x} {e} {p} {X} {Energy}
    ES transition target S radius) →
  (state : X) →
  S state →
  S (transition state)
fejerPreservesSublevel {ES = ES} F state member =
  sublevelToMember F (transition state)
    (EC.Preorder.trans
      (EC.EnergySpace.P ES)
      (FE.FejerPoint.fejer (fejerPoint F) state)
      (memberToSublevel F state member))

iterate :
  ∀ {x} {X : Set x} →
  (X → X) →
  Nat →
  X →
  X
iterate transition zero state = state
iterate transition (suc n) state =
  iterate transition n (transition state)

fejerIteratesPreserveSublevel :
  ∀ {x e p X Energy ES transition target S radius} →
  (F : FejerSublevelInvariant
    {x} {e} {p} {X} {Energy}
    ES transition target S radius) →
  (n : Nat) →
  (state : X) →
  S state →
  S (iterate transition n state)
fejerIteratesPreserveSublevel F zero state member = member
fejerIteratesPreserveSublevel F (suc n) state member =
  fejerIteratesPreserveSublevel F n
    _
    (fejerPreservesSublevel F state member)
