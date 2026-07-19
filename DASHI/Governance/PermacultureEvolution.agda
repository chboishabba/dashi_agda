module DASHI.Governance.PermacultureEvolution where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- A typed governance reading of the three-lane permaculture diagram.
--
-- This module treats the names as labels for candidate governance lanes,
-- not as historical, empirical, moral, or political authority claims.
-- Lane identity is carried jointly by scale, authority, substrate, and
-- directive.  Hectares alone never construct a promotion witness.

------------------------------------------------------------------------
-- Lane coordinates.

data PermacultureLane : Set where
  holmgrenian mollisonian newtonian : PermacultureLane

data ScaleBand : Set where
  microScale macroScale megaScale : ScaleBand

data GovernanceStyle : Set where
  domesticDefensive commercialCompetitor sovereignFoundational :
    GovernanceStyle

data CoreDirective : Set where
  decoupleAndHide replaceAndCompete commandTheBedrock : CoreDirective

data StrategicVector : Set where
  defensive aggressiveReplacement dominantSovereign : StrategicVector

data AuthoritySurface : Set where
  householdOrBlock farmOrCommercialOperator sovereignTerritory :
    AuthoritySurface

data SubstrateBinding : Set where
  domesticPatch productiveLandscape territorialBedrock : SubstrateBinding

record LaneProfile : Set where
  constructor laneProfile
  field
    lane              : PermacultureLane
    scaleBand         : ScaleBand
    governanceStyle   : GovernanceStyle
    directive         : CoreDirective
    strategicVector   : StrategicVector
    authoritySurface  : AuthoritySurface
    substrateBinding  : SubstrateBinding

open LaneProfile public

holmgrenianProfile : LaneProfile
holmgrenianProfile =
  laneProfile
    holmgrenian
    microScale
    domesticDefensive
    decoupleAndHide
    defensive
    householdOrBlock
    domesticPatch

mollisonianProfile : LaneProfile
mollisonianProfile =
  laneProfile
    mollisonian
    macroScale
    commercialCompetitor
    replaceAndCompete
    aggressiveReplacement
    farmOrCommercialOperator
    productiveLandscape

newtonianProfile : LaneProfile
newtonianProfile =
  laneProfile
    newtonian
    megaScale
    sovereignFoundational
    commandTheBedrock
    dominantSovereign
    sovereignTerritory
    territorialBedrock

canonicalProfiles : List LaneProfile
canonicalProfiles =
  holmgrenianProfile ∷ mollisonianProfile ∷ newtonianProfile ∷ []

------------------------------------------------------------------------
-- Evolution graph and the strategic split.

data EvolutionEdge : PermacultureLane -> Set where
  domesticResilienceProjection : EvolutionEdge holmgrenian
  productiveMarketProjection   : EvolutionEdge mollisonian
  sovereignSubstrateProjection : EvolutionEdge newtonian

data SplitLane : Set where
  mollisonianSplit newtonianSplit : SplitLane

splitEmbedding : SplitLane -> PermacultureLane
splitEmbedding mollisonianSplit = mollisonian
splitEmbedding newtonianSplit   = newtonian

data ConflictTarget : Set where
  incumbentProductionLayer foundationalSubstrateLayer : ConflictTarget

splitTarget : SplitLane -> ConflictTarget
splitTarget mollisonianSplit = incumbentProductionLayer
splitTarget newtonianSplit   = foundationalSubstrateLayer

------------------------------------------------------------------------
-- Admission is proof-relevant.  A project enters a lane only by supplying
-- all canonical coordinate equalities for that lane.

record LaneAdmission (profile : LaneProfile) (candidate : LaneProfile) : Set where
  constructor admitLane
  field
    laneMatches       : lane candidate ≡ lane profile
    scaleMatches      : scaleBand candidate ≡ scaleBand profile
    governanceMatches : governanceStyle candidate ≡ governanceStyle profile
    directiveMatches  : directive candidate ≡ directive profile
    vectorMatches     : strategicVector candidate ≡ strategicVector profile
    authorityMatches  : authoritySurface candidate ≡ authoritySurface profile
    substrateMatches  : substrateBinding candidate ≡ substrateBinding profile

open LaneAdmission public

canonicalHolmgrenianAdmission :
  LaneAdmission holmgrenianProfile holmgrenianProfile
canonicalHolmgrenianAdmission =
  admitLane refl refl refl refl refl refl refl

canonicalMollisonianAdmission :
  LaneAdmission mollisonianProfile mollisonianProfile
canonicalMollisonianAdmission =
  admitLane refl refl refl refl refl refl refl

canonicalNewtonianAdmission :
  LaneAdmission newtonianProfile newtonianProfile
canonicalNewtonianAdmission =
  admitLane refl refl refl refl refl refl refl

------------------------------------------------------------------------
-- Promotion is authority-bearing.  There is deliberately no constructor
-- accepting only a ScaleBand equality or a hectare count.

data CommercialProductionAuthority : Set where
  commercialProductionAuthority : CommercialProductionAuthority

data SovereignSubstrateAuthority : Set where
  sovereignSubstrateAuthority : SovereignSubstrateAuthority

data LanePromotion : PermacultureLane -> PermacultureLane -> Set where
  domesticToCommercial :
    CommercialProductionAuthority ->
    LanePromotion holmgrenian mollisonian

  commercialToSovereign :
    SovereignSubstrateAuthority ->
    LanePromotion mollisonian newtonian

promotionCarriesAuthority :
  {from to : PermacultureLane} ->
  LanePromotion from to ->
  ⊤
promotionCarriesAuthority (domesticToCommercial _) = tt
promotionCarriesAuthority (commercialToSovereign _) = tt

scaleOnlyPromotionFlag : Bool
scaleOnlyPromotionFlag = false

scaleOnlyPromotionIsBlocked : scaleOnlyPromotionFlag ≡ false
scaleOnlyPromotionIsBlocked = refl

------------------------------------------------------------------------
-- Distinctness / no false equivalence.

holmgrenianNotMollisonian : holmgrenian ≡ mollisonian -> Set
holmgrenianNotMollisonian ()

mollisonianNotNewtonian : mollisonian ≡ newtonian -> Set
mollisonianNotNewtonian ()

holmgrenianNotNewtonian : holmgrenian ≡ newtonian -> Set
holmgrenianNotNewtonian ()

------------------------------------------------------------------------
-- Compact identity theorem: an admitted candidate exposes every coordinate
-- of the canonical lane profile, rather than reducing identity to scale.

record LaneIdentityReceipt (profile candidate : LaneProfile) : Set where
  constructor laneIdentityReceipt
  field
    admitted : LaneAdmission profile candidate

open LaneIdentityReceipt public

admissionYieldsIdentityReceipt :
  {profile candidate : LaneProfile} ->
  LaneAdmission profile candidate ->
  LaneIdentityReceipt profile candidate
admissionYieldsIdentityReceipt admission = laneIdentityReceipt admission

permacultureEvolutionPromoted : Bool
permacultureEvolutionPromoted = false

permacultureEvolutionPromotedIsFalse :
  permacultureEvolutionPromoted ≡ false
permacultureEvolutionPromotedIsFalse = refl
