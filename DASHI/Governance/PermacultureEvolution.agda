module DASHI.Governance.PermacultureEvolution where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- A source-qualified governance reading of the supplied permaculture
-- evolution diagram.
--
-- The named traditions are lineage labels.  The governance coordinates are
-- projections made by a particular diagram, not definitional historical,
-- empirical, moral, or political truths about those traditions.
--
-- Lane identity is carried jointly by:
--
--   lineage × scale × governance × directive × strategic vector
--           × authority surface × substrate binding.
--
-- Hectares alone never construct admission or promotion.

------------------------------------------------------------------------
-- Named lineage carriers and governance coordinates.

data PermacultureTradition : Set where
  holmgrenian mollisonian newtonian : PermacultureTradition

-- Compatibility alias for the initial diagram formalisation.
PermacultureLane : Set
PermacultureLane = PermacultureTradition

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

record GovernanceProfile : Set where
  constructor governanceProfile
  field
    scaleBand         : ScaleBand
    governanceStyle   : GovernanceStyle
    directive         : CoreDirective
    strategicVector   : StrategicVector
    authoritySurface  : AuthoritySurface
    substrateBinding  : SubstrateBinding

open GovernanceProfile public

record LaneProfile : Set where
  constructor laneProfile
  field
    tradition  : PermacultureTradition
    governance : GovernanceProfile

open LaneProfile public

-- Compatibility projections retaining the original public surface.
lane : LaneProfile -> PermacultureLane
lane = tradition

profileScaleBand : LaneProfile -> ScaleBand
profileScaleBand p = scaleBand (governance p)

profileGovernanceStyle : LaneProfile -> GovernanceStyle
profileGovernanceStyle p = governanceStyle (governance p)

profileDirective : LaneProfile -> CoreDirective
profileDirective p = directive (governance p)

profileStrategicVector : LaneProfile -> StrategicVector
profileStrategicVector p = strategicVector (governance p)

profileAuthoritySurface : LaneProfile -> AuthoritySurface
profileAuthoritySurface p = authoritySurface (governance p)

profileSubstrateBinding : LaneProfile -> SubstrateBinding
profileSubstrateBinding p = substrateBinding (governance p)

holmgrenianGovernance : GovernanceProfile
holmgrenianGovernance =
  governanceProfile
    microScale
    domesticDefensive
    decoupleAndHide
    defensive
    householdOrBlock
    domesticPatch

mollisonianGovernance : GovernanceProfile
mollisonianGovernance =
  governanceProfile
    macroScale
    commercialCompetitor
    replaceAndCompete
    aggressiveReplacement
    farmOrCommercialOperator
    productiveLandscape

newtonianGovernance : GovernanceProfile
newtonianGovernance =
  governanceProfile
    megaScale
    sovereignFoundational
    commandTheBedrock
    dominantSovereign
    sovereignTerritory
    territorialBedrock

holmgrenianProfile : LaneProfile
holmgrenianProfile = laneProfile holmgrenian holmgrenianGovernance

mollisonianProfile : LaneProfile
mollisonianProfile = laneProfile mollisonian mollisonianGovernance

newtonianProfile : LaneProfile
newtonianProfile = laneProfile newtonian newtonianGovernance

canonicalProfiles : List LaneProfile
canonicalProfiles =
  holmgrenianProfile ∷ mollisonianProfile ∷ newtonianProfile ∷ []

------------------------------------------------------------------------
-- Source qualification.
--
-- A projection states only that a source depicts a tradition through a
-- governance profile.  It does not identify the tradition with that profile.

data DiagramSource : Set where
  suppliedPermacultureEvolutionDiagram : DiagramSource

data DiagramPanel : Set where
  evolutionPanel splitPanel : DiagramPanel

record DiagramProjection : Set where
  constructor diagramProjection
  field
    source           : DiagramSource
    panel            : DiagramPanel
    sourceTradition  : PermacultureTradition
    projectedProfile : GovernanceProfile

open DiagramProjection public

holmgrenianDiagramProjection : DiagramProjection
holmgrenianDiagramProjection =
  diagramProjection
    suppliedPermacultureEvolutionDiagram
    evolutionPanel
    holmgrenian
    holmgrenianGovernance

mollisonianEvolutionProjection : DiagramProjection
mollisonianEvolutionProjection =
  diagramProjection
    suppliedPermacultureEvolutionDiagram
    evolutionPanel
    mollisonian
    mollisonianGovernance

newtonianEvolutionProjection : DiagramProjection
newtonianEvolutionProjection =
  diagramProjection
    suppliedPermacultureEvolutionDiagram
    evolutionPanel
    newtonian
    newtonianGovernance

canonicalDiagramProjections : List DiagramProjection
canonicalDiagramProjections =
  holmgrenianDiagramProjection
  ∷ mollisonianEvolutionProjection
  ∷ newtonianEvolutionProjection
  ∷ []

------------------------------------------------------------------------
-- Quantified scale observations.
--
-- Bounds are stored in tenths of a hectare so that 0.1 ha is represented by
-- 1 without importing a rational-number stack.  These are observations of
-- labels printed in the supplied diagram, not promoted scale laws.

record HectareBandObservation : Set where
  constructor hectareBandObservation
  field
    observationSource : DiagramSource
    observationPanel  : DiagramPanel
    observedTradition : PermacultureTradition
    lowerTenthsHa     : Nat
    upperTenthsHa     : Maybe Nat

open HectareBandObservation public

holmgrenianEvolutionScale : HectareBandObservation
holmgrenianEvolutionScale =
  hectareBandObservation
    suppliedPermacultureEvolutionDiagram evolutionPanel holmgrenian 1 (just 10)

mollisonianEvolutionScale : HectareBandObservation
mollisonianEvolutionScale =
  hectareBandObservation
    suppliedPermacultureEvolutionDiagram evolutionPanel mollisonian 10 (just 10000)

newtonianEvolutionScale : HectareBandObservation
newtonianEvolutionScale =
  hectareBandObservation
    suppliedPermacultureEvolutionDiagram evolutionPanel newtonian 10000 nothing

-- The lower split panel prints a different Mollisonian lower bound: 100 ha.
mollisonianSplitScale : HectareBandObservation
mollisonianSplitScale =
  hectareBandObservation
    suppliedPermacultureEvolutionDiagram splitPanel mollisonian 1000 (just 10000)

newtonianSplitScale : HectareBandObservation
newtonianSplitScale =
  hectareBandObservation
    suppliedPermacultureEvolutionDiagram splitPanel newtonian 10000 nothing

mollisonianPanelLowerBoundsDiffer :
  lowerTenthsHa mollisonianEvolutionScale ≡ 10
mollisonianPanelLowerBoundsDiffer = refl

mollisonianSplitLowerBoundIsHundredHa :
  lowerTenthsHa mollisonianSplitScale ≡ 1000
mollisonianSplitLowerBoundIsHundredHa = refl

------------------------------------------------------------------------
-- Evolution graph and strategic split.

data EvolutionEdge : PermacultureTradition -> Set where
  domesticResilienceProjection : EvolutionEdge holmgrenian
  productiveMarketProjection   : EvolutionEdge mollisonian
  sovereignSubstrateProjection : EvolutionEdge newtonian

data SplitLane : Set where
  mollisonianSplit newtonianSplit : SplitLane

splitEmbedding : SplitLane -> PermacultureTradition
splitEmbedding mollisonianSplit = mollisonian
splitEmbedding newtonianSplit   = newtonian

data ConflictTarget : Set where
  incumbentProductionLayer foundationalSubstrateLayer : ConflictTarget

splitTarget : SplitLane -> ConflictTarget
splitTarget mollisonianSplit = incumbentProductionLayer
splitTarget newtonianSplit   = foundationalSubstrateLayer

------------------------------------------------------------------------
-- Admission is proof-relevant.  A candidate enters a source-projected lane
-- only by supplying equality receipts for every coordinate.

record LaneAdmission (profile candidate : LaneProfile) : Set where
  constructor admitLane
  field
    traditionMatches  : tradition candidate ≡ tradition profile
    scaleMatches      : profileScaleBand candidate ≡ profileScaleBand profile
    governanceMatches :
      profileGovernanceStyle candidate ≡ profileGovernanceStyle profile
    directiveMatches  : profileDirective candidate ≡ profileDirective profile
    vectorMatches     :
      profileStrategicVector candidate ≡ profileStrategicVector profile
    authorityMatches  :
      profileAuthoritySurface candidate ≡ profileAuthoritySurface profile
    substrateMatches  :
      profileSubstrateBinding candidate ≡ profileSubstrateBinding profile

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

-- Extensional closure: matching all coordinates reconstructs profile equality.
admissionImpliesProfileEquality :
  {profile candidate : LaneProfile} ->
  LaneAdmission profile candidate ->
  candidate ≡ profile
admissionImpliesProfileEquality
  {laneProfile t (governanceProfile s g d v a b)}
  {laneProfile .t (governanceProfile .s .g .d .v .a .b)}
  (admitLane refl refl refl refl refl refl refl) = refl

------------------------------------------------------------------------
-- Promotion is authority-bearing.  There is deliberately no constructor
-- accepting only a ScaleBand equality or a hectare count.

data CommercialProductionAuthority : Set where
  commercialProductionAuthority : CommercialProductionAuthority

data SovereignSubstrateAuthority : Set where
  sovereignSubstrateAuthority : SovereignSubstrateAuthority

data LanePromotion : PermacultureTradition -> PermacultureTradition -> Set where
  domesticToCommercial :
    CommercialProductionAuthority ->
    LanePromotion holmgrenian mollisonian

  commercialToSovereign :
    SovereignSubstrateAuthority ->
    LanePromotion mollisonian newtonian

data PromotionAuthority :
  PermacultureTradition -> PermacultureTradition -> Set where

  commercialAuthority :
    CommercialProductionAuthority ->
    PromotionAuthority holmgrenian mollisonian

  sovereignAuthority :
    SovereignSubstrateAuthority ->
    PromotionAuthority mollisonian newtonian

promotionAuthority :
  {from to : PermacultureTradition} ->
  LanePromotion from to ->
  PromotionAuthority from to
promotionAuthority (domesticToCommercial authority) =
  commercialAuthority authority
promotionAuthority (commercialToSovereign authority) =
  sovereignAuthority authority

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
-- Compact identity and source receipts.

record LaneIdentityReceipt (profile candidate : LaneProfile) : Set where
  constructor laneIdentityReceipt
  field
    admitted       : LaneAdmission profile candidate
    profileEquality : candidate ≡ profile

open LaneIdentityReceipt public

admissionYieldsIdentityReceipt :
  {profile candidate : LaneProfile} ->
  LaneAdmission profile candidate ->
  LaneIdentityReceipt profile candidate
admissionYieldsIdentityReceipt admission =
  laneIdentityReceipt admission (admissionImpliesProfileEquality admission)

record PermacultureDiagramBundle : Set where
  constructor permacultureDiagramBundle
  field
    lineageProfiles       : List LaneProfile
    sourceProjections     : List DiagramProjection
    evolutionScales      : List HectareBandObservation
    strategicSplitScales : List HectareBandObservation
    mollisonianTarget     : splitTarget mollisonianSplit ≡ incumbentProductionLayer
    newtonianTarget       : splitTarget newtonianSplit ≡ foundationalSubstrateLayer
    scaleOnlyBlocked      : scaleOnlyPromotionFlag ≡ false

open PermacultureDiagramBundle public

canonicalPermacultureDiagramBundle : PermacultureDiagramBundle
canonicalPermacultureDiagramBundle =
  permacultureDiagramBundle
    canonicalProfiles
    canonicalDiagramProjections
    (holmgrenianEvolutionScale
      ∷ mollisonianEvolutionScale
      ∷ newtonianEvolutionScale
      ∷ [])
    (mollisonianSplitScale ∷ newtonianSplitScale ∷ [])
    refl
    refl
    refl

------------------------------------------------------------------------
-- Governance boundary.
--
-- The supplied image has now been encoded as a source-bound candidate lens.
-- Historical accuracy, empirical universality, moral rank, and political
-- authority remain unpromoted.

historicalCharacterisationPromoted : Bool
historicalCharacterisationPromoted = false

empiricalUniversalityPromoted : Bool
empiricalUniversalityPromoted = false

moralHierarchyPromoted : Bool
moralHierarchyPromoted = false

politicalAuthorityPromoted : Bool
politicalAuthorityPromoted = false

permacultureEvolutionPromoted : Bool
permacultureEvolutionPromoted = false

historicalCharacterisationPromotedIsFalse :
  historicalCharacterisationPromoted ≡ false
historicalCharacterisationPromotedIsFalse = refl

empiricalUniversalityPromotedIsFalse :
  empiricalUniversalityPromoted ≡ false
empiricalUniversalityPromotedIsFalse = refl

moralHierarchyPromotedIsFalse : moralHierarchyPromoted ≡ false
moralHierarchyPromotedIsFalse = refl

politicalAuthorityPromotedIsFalse : politicalAuthorityPromoted ≡ false
politicalAuthorityPromotedIsFalse = refl

permacultureEvolutionPromotedIsFalse :
  permacultureEvolutionPromoted ≡ false
permacultureEvolutionPromotedIsFalse = refl
