module DASHI.Vision.Surfel.CoreExpansion where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Vision.Surfel.PromotionOrder

infixr 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,×_
  field
    fst : A
    snd : B

open _×_ public

record SurfelCarrier : Set₁ where
  field
    Surfel : Set
    state : Surfel → SurfelState
    sameCluster : Surfel → Surfel → Set
    mergeAdmissible : Surfel → Surfel → Set

open SurfelCarrier public

data CoreExpandedSelection (C : SurfelCarrier) : Surfel C → Set where
  selectedCore :
    {s : Surfel C} →
    state C s ≡ ascended →
    CoreExpandedSelection C s

  selectedPlateau :
    {s : Surfel C} →
    state C s ≡ plateau →
    (Σ (Surfel C) λ anchor →
       state C anchor ≡ ascended
       × sameCluster C anchor s
       × mergeAdmissible C anchor s) →
    CoreExpandedSelection C s

ascended≢plateau : ascended ≡ plateau → ⊥
ascended≢plateau ()

plateauSelectionHasAscendedAnchor :
  {C : SurfelCarrier} →
  {s : Surfel C} →
  CoreExpandedSelection C s →
  state C s ≡ plateau →
  Σ (Surfel C) λ anchor →
    state C anchor ≡ ascended
    × sameCluster C anchor s
    × mergeAdmissible C anchor s
plateauSelectionHasAscendedAnchor (selectedCore core) plateauEq =
  ⊥-elim (ascended≢plateau (trans (sym core) plateauEq))
plateauSelectionHasAscendedAnchor (selectedPlateau _ anchored) _ = anchored

record PromotedCluster (C : SurfelCarrier) : Set₁ where
  field
    Member : Surfel C → Set
    ascendedAnchor :
      Σ (Surfel C) λ s →
        Member s × state C s ≡ ascended
    closedUnderSelection :
      {s : Surfel C} →
      Member s →
      CoreExpandedSelection C s

open PromotedCluster public

promotedClusterHasAscendedMember :
  {C : SurfelCarrier} →
  (cluster : PromotedCluster C) →
  Σ (Surfel C) λ s →
    Member cluster s × state C s ≡ ascended
promotedClusterHasAscendedMember cluster = ascendedAnchor cluster

data PlateauOnlyPromotionAuthority : Set where

plateauOnlyPromotionImpossible :
  PlateauOnlyPromotionAuthority →
  ⊥
plateauOnlyPromotionImpossible ()
