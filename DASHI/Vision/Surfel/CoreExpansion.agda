module DASHI.Vision.Surfel.CoreExpansion where

open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Vision.Surfel.PromotionOrder

------------------------------------------------------------------------
-- Abstract surfel carrier and cluster membership.

record SurfelCarrier : Set₁ where
  field
    Surfel : Set
    state : Surfel → SurfelState
    sameCluster : Surfel → Surfel → Set
    mergeAdmissible : Surfel → Surfel → Set

open SurfelCarrier public

------------------------------------------------------------------------
-- Selection is core-first.  Plateau surfels may enter only through an
-- ascended anchor in the same admissible cluster.

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

------------------------------------------------------------------------
-- Local product, kept here to avoid importing a large product surface.

infixr 4 _×_
record _×_ (A B : Set) : Set where
  constructor _,×_
  field
    fst : A
    snd : B

open _×_ public

------------------------------------------------------------------------
-- Every selected non-core surfel carries an explicit ascended anchor.

plateauSelectionHasAscendedAnchor :
  {C : SurfelCarrier} →
  {s : Surfel C} →
  CoreExpandedSelection C s →
  state C s ≡ plateau →
  Σ (Surfel C) λ anchor →
    state C anchor ≡ ascended
    × sameCluster C anchor s
    × mergeAdmissible C anchor s
plateauSelectionHasAscendedAnchor (selectedCore core) plateauEq with core
... | ()
plateauSelectionHasAscendedAnchor (selectedPlateau _ anchored) _ = anchored

------------------------------------------------------------------------
-- Cluster promotion therefore requires at least one ascended member.

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

------------------------------------------------------------------------
-- No raw plateau-only cluster can be promoted through this interface.

data PlateauOnlyPromotionAuthority : Set where

plateauOnlyPromotionImpossible :
  PlateauOnlyPromotionAuthority →
  Data.Empty.⊥
plateauOnlyPromotionImpossible ()
