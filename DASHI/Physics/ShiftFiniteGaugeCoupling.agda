module DASHI.Physics.ShiftFiniteGaugeCoupling where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Integer using (-[1+_])
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI
open import DASHI.Physics.ShiftDiscreteWaveStep as SDWS
open import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
open import DASHI.Physics.ShiftPhaseTableInterference as SPTI4
open import DASHI.Physics.ShiftSpatialLaplacian as SSL

------------------------------------------------------------------------
-- First finite matter+gauge lift over the current shift-wave lane.
--
-- Gauge data stays bounded and static in this lane: one Phase4 link phase per
-- coarse carrier point, interpreted as the phase transport toward the right
-- neighbor. The result is a theorem-thin covariant operator/update surface,
-- not a full lattice gauge theory or dynamic-gauge package.

cong :
  {A B : Set} →
  (f : A → B) →
  {x y : A} →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

GaugeField : Set
GaugeField = SPTI.ShiftPressurePoint → SPTI4.Phase4

vacuumGaugeField : GaugeField
vacuumGaugeField _ = SPTI4.φ0

SFGCSite : Set
SFGCSite = SPTI.ShiftPressurePoint

data SFGCPrimeDirection : Set where
  p2Right :
    SFGCPrimeDirection

  p3Transverse :
    SFGCPrimeDirection

data SFGCShiftEdge : SFGCPrimeDirection → SFGCSite → Set where
  sfgcP2RightEdgeAt :
    (site : SFGCSite) →
    SFGCShiftEdge p2Right site

_≠_ : {A : Set} → A → A → Set
x ≠ y = x ≡ y → ⊥

p2Right≠p3Transverse :
  p2Right ≠ p3Transverse
p2Right≠p3Transverse ()

shiftNextPoint≠shiftStartPoint :
  SPTI.shiftNextPoint ≠ SPTI.shiftStartPoint
shiftNextPoint≠shiftStartPoint ()

sfgcShiftEdgeSource :
  {dir : SFGCPrimeDirection} →
  {site : SFGCSite} →
  SFGCShiftEdge dir site →
  SFGCSite
sfgcShiftEdgeSource (sfgcP2RightEdgeAt site) =
  site

sfgcShiftEdgeTarget :
  {dir : SFGCPrimeDirection} →
  {site : SFGCSite} →
  SFGCShiftEdge dir site →
  SFGCSite
sfgcShiftEdgeTarget (sfgcP2RightEdgeAt site) =
  SSL.rightNeighbor site

sfgcShiftEdgeSourceLaw :
  {dir : SFGCPrimeDirection} →
  (site : SFGCSite) →
  (edge : SFGCShiftEdge dir site) →
  sfgcShiftEdgeSource edge ≡ site
sfgcShiftEdgeSourceLaw site (sfgcP2RightEdgeAt .site) =
  refl

sfgcP2ShiftEdgeTargetLaw :
  (site : SFGCSite) →
  sfgcShiftEdgeTarget (sfgcP2RightEdgeAt site) ≡ SSL.rightNeighbor site
sfgcP2ShiftEdgeTargetLaw site =
  refl

sfgcP3TransverseShiftEdgeMissing :
  (site : SFGCSite) →
  SFGCShiftEdge p3Transverse site →
  ⊥
sfgcP3TransverseShiftEdgeMissing site ()

leftNeighborCannotBeP3Transverse :
  SSL.rightNeighbor (SSL.leftNeighbor SPTI.shiftStartPoint)
    ≠
  SSL.leftNeighbor (SSL.rightNeighbor SPTI.shiftStartPoint)
leftNeighborCannotBeP3Transverse =
  shiftNextPoint≠shiftStartPoint

record SFGCThreePointP3ActionObstruction : Set₁ where
  field
    inspectedSiteCarrier :
      Set

    inspectedSiteCarrierIsCurrentShiftPressurePoint :
      inspectedSiteCarrier ≡ SPTI.ShiftPressurePoint

    rightAction :
      SFGCSite →
      SFGCSite

    rightActionIsCurrentEndpointAction :
      rightAction ≡ SSL.rightNeighbor

    reflectedLeftAction :
      SFGCSite →
      SFGCSite

    reflectedLeftActionIsCurrentLeftNeighbor :
      reflectedLeftAction ≡ SSL.leftNeighbor

    reflectedLeftFailsP2P3CommutationAtStart :
      rightAction (reflectedLeftAction SPTI.shiftStartPoint)
        ≠
      reflectedLeftAction (rightAction SPTI.shiftStartPoint)

    exactFiniteCarrierObstruction :
      List String

    exactUpstreamConstructNeeded :
      List String

canonicalSFGCThreePointP3ActionObstruction :
  SFGCThreePointP3ActionObstruction
canonicalSFGCThreePointP3ActionObstruction =
  record
    { inspectedSiteCarrier =
        SPTI.ShiftPressurePoint
    ; inspectedSiteCarrierIsCurrentShiftPressurePoint =
        refl
    ; rightAction =
        SSL.rightNeighbor
    ; rightActionIsCurrentEndpointAction =
        refl
    ; reflectedLeftAction =
        SSL.leftNeighbor
    ; reflectedLeftActionIsCurrentLeftNeighbor =
        refl
    ; reflectedLeftFailsP2P3CommutationAtStart =
        leftNeighborCannotBeP3Transverse
    ; exactFiniteCarrierObstruction =
        "SSL.leftNeighbor cannot be the p3 transverse action: right(left shiftStartPoint) = shiftNextPoint but left(right shiftStartPoint) = shiftStartPoint"
        ∷ "SSL.rightNeighbor cannot be reused as p3Transverse without identifying the p2 and p3 edges"
        ∷ "The identity action commutes with SSL.rightNeighbor but is degenerate and creates no transverse plaquette"
        ∷ "A constant/collapse-to-exit action commutes with SSL.rightNeighbor but is degenerate and cannot witness a nondegenerate p3 direction"
        ∷ "The current three-constructor ShiftPressurePoint carrier has no prime coordinate, p3 endpoint, or second independent axis"
        ∷ []
    ; exactUpstreamConstructNeeded =
        "A real p3 shift action over SFGCSite supplied from an extended carrier, not from ShiftPressurePoint record projections"
        ∷ "A p3 edge constructor or equivalent endpoint API that inhabits SFGCShiftEdge p3Transverse site"
        ∷ "A p3 endpoint law relating sfgcShiftEdgeTarget of that edge to the supplied p3 shift action"
        ∷ "A p2/p3 endpoint commutation law over the same SFGCSite carrier"
        ∷ "A nondegeneracy law proving the p3 action is not rightNeighbor, leftNeighbor, identity, or collapse-only"
        ∷ []
    }

record SFGCTransverseP3LinkUpstreamAPIRequest : Set₁ where
  field
    siteCarrier :
      Set

    siteCarrierIsCurrentShiftPressurePoint :
      siteCarrier ≡ SPTI.ShiftPressurePoint

    currentConcreteSiteConstructors :
      List String

    currentSiteEndpointStructure :
      List String

    rightDirection :
      SFGCPrimeDirection

    rightDirectionIsP2 :
      rightDirection ≡ p2Right

    transverseDirection :
      SFGCPrimeDirection

    transverseDirectionIsP3 :
      transverseDirection ≡ p3Transverse

    currentRightLinkAt :
      (site : SFGCSite) →
      SFGCShiftEdge p2Right site

    currentRightEndpoint :
      (site : SFGCSite) →
      sfgcShiftEdgeTarget (currentRightLinkAt site)
        ≡
      SSL.rightNeighbor site

    transverseLinkStillUninhabited :
      (site : SFGCSite) →
      SFGCShiftEdge p3Transverse site →
      ⊥

    threePointP3ActionObstruction :
      SFGCThreePointP3ActionObstruction

    requestedUpstreamAPI :
      List String

    failClosedReason :
      List String

record SFGCMinimalP3SemanticExtensionAPI : Set₁ where
  field
    ExtendedSFGCSite :
      Set

    embedCurrentSite :
      SFGCSite →
      ExtendedSFGCSite

    p2ShiftAction :
      ExtendedSFGCSite →
      ExtendedSFGCSite

    p3ShiftAction :
      ExtendedSFGCSite →
      ExtendedSFGCSite

    ExtendedSFGCShiftEdge :
      SFGCPrimeDirection →
      ExtendedSFGCSite →
      Set

    extendedP2RightLinkAt :
      (site : ExtendedSFGCSite) →
      ExtendedSFGCShiftEdge p2Right site

    extendedP3TransverseLinkAt :
      (site : ExtendedSFGCSite) →
      ExtendedSFGCShiftEdge p3Transverse site

    extendedEdgeSource :
      {dir : SFGCPrimeDirection} →
      {site : ExtendedSFGCSite} →
      ExtendedSFGCShiftEdge dir site →
      ExtendedSFGCSite

    extendedEdgeTarget :
      {dir : SFGCPrimeDirection} →
      {site : ExtendedSFGCSite} →
      ExtendedSFGCShiftEdge dir site →
      ExtendedSFGCSite

    extendedEdgeSourceLaw :
      {dir : SFGCPrimeDirection} →
      (site : ExtendedSFGCSite) →
      (edge : ExtendedSFGCShiftEdge dir site) →
      extendedEdgeSource edge ≡ site

    extendedP2TargetLaw :
      (site : ExtendedSFGCSite) →
      extendedEdgeTarget (extendedP2RightLinkAt site)
        ≡
      p2ShiftAction site

    extendedP3TargetLaw :
      (site : ExtendedSFGCSite) →
      extendedEdgeTarget (extendedP3TransverseLinkAt site)
        ≡
      p3ShiftAction site

    p2ThenP3 :
      ExtendedSFGCSite →
      ExtendedSFGCSite

    p3ThenP2 :
      ExtendedSFGCSite →
      ExtendedSFGCSite

    p2ThenP3Law :
      (site : ExtendedSFGCSite) →
      p2ThenP3 site
        ≡
      p3ShiftAction (p2ShiftAction site)

    p3ThenP2Law :
      (site : ExtendedSFGCSite) →
      p3ThenP2 site
        ≡
      p2ShiftAction (p3ShiftAction site)

    p2p3EndpointCommutation :
      (site : ExtendedSFGCSite) →
      p2ThenP3 site ≡ p3ThenP2 site

    currentRightCompatibility :
      (site : SFGCSite) →
      p2ShiftAction (embedCurrentSite site)
        ≡
      embedCurrentSite (SSL.rightNeighbor site)

    p3NotCurrentRightAction :
      p3ShiftAction ≠ p2ShiftAction

    p3NotCurrentLeftActionOnEmbeddedSites :
      (λ site → p3ShiftAction (embedCurrentSite site))
        ≠
      (λ site → embedCurrentSite (SSL.leftNeighbor site))

    p3NotIdentityAction :
      p3ShiftAction ≠ (λ site → site)

    nondegenerateBoundary :
      List String

data SFGCSite2D : Set where
  sfgcSite2D :
    SPTI.ShiftPressurePoint →
    SPTI.ShiftPressurePoint →
    SFGCSite2D

embedCurrentSite2D :
  SFGCSite →
  SFGCSite2D
embedCurrentSite2D site =
  sfgcSite2D site SPTI.shiftStartPoint

sfgcSite2DP2ShiftAction :
  SFGCSite2D →
  SFGCSite2D
sfgcSite2DP2ShiftAction (sfgcSite2D p2 p3) =
  sfgcSite2D (SSL.rightNeighbor p2) p3

sfgcSite2DP3ShiftAction :
  SFGCSite2D →
  SFGCSite2D
sfgcSite2DP3ShiftAction (sfgcSite2D p2 p3) =
  sfgcSite2D p2 (SSL.rightNeighbor p3)

data SFGCSite2DShiftEdge :
  SFGCPrimeDirection →
  SFGCSite2D →
  Set where
  sfgcSite2DP2RightEdgeAt :
    (site : SFGCSite2D) →
    SFGCSite2DShiftEdge p2Right site

  sfgcSite2DP3TransverseEdgeAt :
    (site : SFGCSite2D) →
    SFGCSite2DShiftEdge p3Transverse site

sfgcSite2DEdgeSource :
  {dir : SFGCPrimeDirection} →
  {site : SFGCSite2D} →
  SFGCSite2DShiftEdge dir site →
  SFGCSite2D
sfgcSite2DEdgeSource (sfgcSite2DP2RightEdgeAt site) =
  site
sfgcSite2DEdgeSource (sfgcSite2DP3TransverseEdgeAt site) =
  site

sfgcSite2DEdgeTarget :
  {dir : SFGCPrimeDirection} →
  {site : SFGCSite2D} →
  SFGCSite2DShiftEdge dir site →
  SFGCSite2D
sfgcSite2DEdgeTarget (sfgcSite2DP2RightEdgeAt site) =
  sfgcSite2DP2ShiftAction site
sfgcSite2DEdgeTarget (sfgcSite2DP3TransverseEdgeAt site) =
  sfgcSite2DP3ShiftAction site

sfgcSite2DEdgeSourceLaw :
  {dir : SFGCPrimeDirection} →
  (site : SFGCSite2D) →
  (edge : SFGCSite2DShiftEdge dir site) →
  sfgcSite2DEdgeSource edge ≡ site
sfgcSite2DEdgeSourceLaw site (sfgcSite2DP2RightEdgeAt .site) =
  refl
sfgcSite2DEdgeSourceLaw site (sfgcSite2DP3TransverseEdgeAt .site) =
  refl

sfgcSite2DP2TargetLaw :
  (site : SFGCSite2D) →
  sfgcSite2DEdgeTarget (sfgcSite2DP2RightEdgeAt site)
    ≡
  sfgcSite2DP2ShiftAction site
sfgcSite2DP2TargetLaw site =
  refl

sfgcSite2DP3TargetLaw :
  (site : SFGCSite2D) →
  sfgcSite2DEdgeTarget (sfgcSite2DP3TransverseEdgeAt site)
    ≡
  sfgcSite2DP3ShiftAction site
sfgcSite2DP3TargetLaw site =
  refl

sfgcSite2DP2ThenP3 :
  SFGCSite2D →
  SFGCSite2D
sfgcSite2DP2ThenP3 site =
  sfgcSite2DP3ShiftAction (sfgcSite2DP2ShiftAction site)

sfgcSite2DP3ThenP2 :
  SFGCSite2D →
  SFGCSite2D
sfgcSite2DP3ThenP2 site =
  sfgcSite2DP2ShiftAction (sfgcSite2DP3ShiftAction site)

sfgcSite2DP2ThenP3Law :
  (site : SFGCSite2D) →
  sfgcSite2DP2ThenP3 site
    ≡
  sfgcSite2DP3ShiftAction (sfgcSite2DP2ShiftAction site)
sfgcSite2DP2ThenP3Law site =
  refl

sfgcSite2DP3ThenP2Law :
  (site : SFGCSite2D) →
  sfgcSite2DP3ThenP2 site
    ≡
  sfgcSite2DP2ShiftAction (sfgcSite2DP3ShiftAction site)
sfgcSite2DP3ThenP2Law site =
  refl

sfgcSite2DP2P3EndpointCommutation :
  (site : SFGCSite2D) →
  sfgcSite2DP2ThenP3 site ≡ sfgcSite2DP3ThenP2 site
sfgcSite2DP2P3EndpointCommutation (sfgcSite2D p2 p3) =
  refl

sfgcSite2DCurrentRightCompatibility :
  (site : SFGCSite) →
  sfgcSite2DP2ShiftAction (embedCurrentSite2D site)
    ≡
  embedCurrentSite2D (SSL.rightNeighbor site)
sfgcSite2DCurrentRightCompatibility site =
  refl

sfgcSite2DStartNext≠NextStart :
  sfgcSite2D SPTI.shiftStartPoint SPTI.shiftNextPoint
    ≠
  sfgcSite2D SPTI.shiftNextPoint SPTI.shiftStartPoint
sfgcSite2DStartNext≠NextStart ()

sfgcSite2DStartNext≠StartStart :
  sfgcSite2D SPTI.shiftStartPoint SPTI.shiftNextPoint
    ≠
  sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint
sfgcSite2DStartNext≠StartStart ()

sfgcSite2DP3NotCurrentRightAction :
  sfgcSite2DP3ShiftAction ≠ sfgcSite2DP2ShiftAction
sfgcSite2DP3NotCurrentRightAction sameAction =
  sfgcSite2DStartNext≠NextStart
    (cong
      (λ action →
        action
          (sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint))
      sameAction)

sfgcSite2DP3NotCurrentLeftActionOnEmbeddedSites :
  (λ site → sfgcSite2DP3ShiftAction (embedCurrentSite2D site))
    ≠
  (λ site → embedCurrentSite2D (SSL.leftNeighbor site))
sfgcSite2DP3NotCurrentLeftActionOnEmbeddedSites sameAction =
  sfgcSite2DStartNext≠StartStart
    (cong (λ action → action SPTI.shiftStartPoint) sameAction)

sfgcSite2DP3NotIdentityAction :
  sfgcSite2DP3ShiftAction ≠ (λ site → site)
sfgcSite2DP3NotIdentityAction sameAction =
  sfgcSite2DStartNext≠StartStart
    (cong
      (λ action →
        action
          (sfgcSite2D SPTI.shiftStartPoint SPTI.shiftStartPoint))
      sameAction)

sfgcSite2DShiftAction :
  SFGCPrimeDirection →
  SFGCSite2D →
  SFGCSite2D
sfgcSite2DShiftAction p2Right =
  sfgcSite2DP2ShiftAction
sfgcSite2DShiftAction p3Transverse =
  sfgcSite2DP3ShiftAction

sfgcSite2DShiftEdgeAt :
  (dir : SFGCPrimeDirection) →
  (site : SFGCSite2D) →
  SFGCSite2DShiftEdge dir site
sfgcSite2DShiftEdgeAt p2Right site =
  sfgcSite2DP2RightEdgeAt site
sfgcSite2DShiftEdgeAt p3Transverse site =
  sfgcSite2DP3TransverseEdgeAt site

data SFGCSite2DEdge : Set where
  sfgcSite2DOrientedEdge :
    (dir : SFGCPrimeDirection) →
    (site : SFGCSite2D) →
    SFGCSite2DShiftEdge dir site →
    SFGCSite2DEdge

sfgcSite2DEdgeAt :
  SFGCPrimeDirection →
  SFGCSite2D →
  SFGCSite2DEdge
sfgcSite2DEdgeAt dir site =
  sfgcSite2DOrientedEdge dir site (sfgcSite2DShiftEdgeAt dir site)

sfgcSite2DEdgeSourceTotal :
  SFGCSite2DEdge →
  SFGCSite2D
sfgcSite2DEdgeSourceTotal (sfgcSite2DOrientedEdge dir site edge) =
  sfgcSite2DEdgeSource edge

sfgcSite2DEdgeTargetTotal :
  SFGCSite2DEdge →
  SFGCSite2D
sfgcSite2DEdgeTargetTotal (sfgcSite2DOrientedEdge dir site edge) =
  sfgcSite2DEdgeTarget edge

sfgcSite2DEdgeAtSourceLaw :
  (dir : SFGCPrimeDirection) →
  (site : SFGCSite2D) →
  sfgcSite2DEdgeSourceTotal (sfgcSite2DEdgeAt dir site) ≡ site
sfgcSite2DEdgeAtSourceLaw p2Right site =
  refl
sfgcSite2DEdgeAtSourceLaw p3Transverse site =
  refl

sfgcSite2DEdgeAtTargetLaw :
  (dir : SFGCPrimeDirection) →
  (site : SFGCSite2D) →
  sfgcSite2DEdgeTargetTotal (sfgcSite2DEdgeAt dir site)
    ≡
  sfgcSite2DShiftAction dir site
sfgcSite2DEdgeAtTargetLaw p2Right site =
  refl
sfgcSite2DEdgeAtTargetLaw p3Transverse site =
  refl

data SFGCSite2DPlaquette : Set where
  sfgcSite2DPlaquetteAt :
    SFGCSite2D →
    SFGCSite2DPlaquette

sfgcSite2DPlaquetteSW :
  SFGCSite2DPlaquette →
  SFGCSite2D
sfgcSite2DPlaquetteSW (sfgcSite2DPlaquetteAt base) =
  base

sfgcSite2DPlaquetteSE :
  SFGCSite2DPlaquette →
  SFGCSite2D
sfgcSite2DPlaquetteSE (sfgcSite2DPlaquetteAt base) =
  sfgcSite2DP2ShiftAction base

sfgcSite2DPlaquetteNW :
  SFGCSite2DPlaquette →
  SFGCSite2D
sfgcSite2DPlaquetteNW (sfgcSite2DPlaquetteAt base) =
  sfgcSite2DP3ShiftAction base

sfgcSite2DPlaquetteNE :
  SFGCSite2DPlaquette →
  SFGCSite2D
sfgcSite2DPlaquetteNE (sfgcSite2DPlaquetteAt base) =
  sfgcSite2DP2ThenP3 base

sfgcSite2DPlaquetteBottomEdge :
  SFGCSite2DPlaquette →
  SFGCSite2DEdge
sfgcSite2DPlaquetteBottomEdge (sfgcSite2DPlaquetteAt base) =
  sfgcSite2DEdgeAt p2Right base

sfgcSite2DPlaquetteRightEdge :
  SFGCSite2DPlaquette →
  SFGCSite2DEdge
sfgcSite2DPlaquetteRightEdge plaquette =
  sfgcSite2DEdgeAt p3Transverse (sfgcSite2DPlaquetteSE plaquette)

sfgcSite2DPlaquetteTopEdge :
  SFGCSite2DPlaquette →
  SFGCSite2DEdge
sfgcSite2DPlaquetteTopEdge plaquette =
  sfgcSite2DEdgeAt p2Right (sfgcSite2DPlaquetteNW plaquette)

sfgcSite2DPlaquetteLeftEdge :
  SFGCSite2DPlaquette →
  SFGCSite2DEdge
sfgcSite2DPlaquetteLeftEdge (sfgcSite2DPlaquetteAt base) =
  sfgcSite2DEdgeAt p3Transverse base

sfgcSite2DPlaquetteBottomSourceLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeSourceTotal
    (sfgcSite2DPlaquetteBottomEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteSW (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteBottomSourceLaw base =
  refl

sfgcSite2DPlaquetteBottomTargetLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeTargetTotal
    (sfgcSite2DPlaquetteBottomEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteSE (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteBottomTargetLaw base =
  refl

sfgcSite2DPlaquetteRightSourceLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeSourceTotal
    (sfgcSite2DPlaquetteRightEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteSE (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteRightSourceLaw base =
  refl

sfgcSite2DPlaquetteRightTargetLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeTargetTotal
    (sfgcSite2DPlaquetteRightEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteNE (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteRightTargetLaw base =
  refl

sfgcSite2DPlaquetteTopSourceLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeSourceTotal
    (sfgcSite2DPlaquetteTopEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteNW (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteTopSourceLaw base =
  refl

sfgcSite2DPlaquetteTopTargetLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeTargetTotal
    (sfgcSite2DPlaquetteTopEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteNE (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteTopTargetLaw (sfgcSite2D p2 p3) =
  refl

sfgcSite2DPlaquetteLeftSourceLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeSourceTotal
    (sfgcSite2DPlaquetteLeftEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteSW (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteLeftSourceLaw base =
  refl

sfgcSite2DPlaquetteLeftTargetLaw :
  (base : SFGCSite2D) →
  sfgcSite2DEdgeTargetTotal
    (sfgcSite2DPlaquetteLeftEdge (sfgcSite2DPlaquetteAt base))
    ≡
  sfgcSite2DPlaquetteNW (sfgcSite2DPlaquetteAt base)
sfgcSite2DPlaquetteLeftTargetLaw base =
  refl

sfgcSite2DPrimaryCoordinate :
  SFGCSite2D →
  SFGCSite
sfgcSite2DPrimaryCoordinate (sfgcSite2D p2 p3) =
  p2

sfgcSite2DTransverseCoordinate :
  SFGCSite2D →
  SFGCSite
sfgcSite2DTransverseCoordinate (sfgcSite2D p2 p3) =
  p3

SFGCSite2DDiscrete0Form : Set
SFGCSite2DDiscrete0Form =
  SFGCSite2D → SPTI4.Phase4

data SFGCSite2DDiscrete1Form : Set where
  sfgcSite2DExact1Form :
    SFGCSite2DDiscrete0Form →
    SFGCSite2DDiscrete1Form

  sfgcSite2DConnection1Form :
    GaugeField →
    SFGCSite2DDiscrete1Form

  sfgcSite2DArbitrary1Form :
    (SFGCSite2DEdge → SPTI4.Phase4) →
    SFGCSite2DDiscrete1Form

sfgcSite2DEvaluate1 :
  SFGCSite2DDiscrete1Form →
  SFGCSite2DEdge →
  SPTI4.Phase4
sfgcSite2DEvaluate1 (sfgcSite2DExact1Form f) edge =
  SFGS.phaseAdd4
    (f (sfgcSite2DEdgeTargetTotal edge))
    (SFGS.phaseInv4 (f (sfgcSite2DEdgeSourceTotal edge)))
sfgcSite2DEvaluate1
  (sfgcSite2DConnection1Form A)
  (sfgcSite2DOrientedEdge p2Right site edge) =
  A (sfgcSite2DPrimaryCoordinate site)
sfgcSite2DEvaluate1
  (sfgcSite2DConnection1Form A)
  (sfgcSite2DOrientedEdge p3Transverse site edge) =
  A (sfgcSite2DTransverseCoordinate site)
sfgcSite2DEvaluate1 (sfgcSite2DArbitrary1Form evaluate) edge =
  evaluate edge

sfgcSite2DWilsonLoopPhase :
  SFGCSite2DDiscrete1Form →
  SFGCSite2DPlaquette →
  SPTI4.Phase4
sfgcSite2DWilsonLoopPhase a plaquette =
  SFGS.phaseAdd4
    (SFGS.phaseAdd4
      (SFGS.phaseAdd4
        (sfgcSite2DEvaluate1 a
          (sfgcSite2DPlaquetteBottomEdge plaquette))
        (sfgcSite2DEvaluate1 a
          (sfgcSite2DPlaquetteRightEdge plaquette)))
      (SFGS.phaseInv4
        (sfgcSite2DEvaluate1 a
          (sfgcSite2DPlaquetteTopEdge plaquette))))
    (SFGS.phaseInv4
      (sfgcSite2DEvaluate1 a
        (sfgcSite2DPlaquetteLeftEdge plaquette)))

data SFGCSite2DDiscrete2Form : Set where
  sfgcSite2DZero2Form :
    SFGCSite2DDiscrete2Form

  sfgcSite2DWilsonLoopCurvature :
    SFGCSite2DDiscrete1Form →
    SFGCSite2DDiscrete2Form

  sfgcSite2DArbitrary2Form :
    (SFGCSite2DPlaquette → SPTI4.Phase4) →
    SFGCSite2DDiscrete2Form

sfgcSite2DEvaluate2 :
  SFGCSite2DDiscrete2Form →
  SFGCSite2DPlaquette →
  SPTI4.Phase4
sfgcSite2DEvaluate2 sfgcSite2DZero2Form plaquette =
  SPTI4.φ0
sfgcSite2DEvaluate2 (sfgcSite2DWilsonLoopCurvature a) plaquette =
  sfgcSite2DWilsonLoopPhase a plaquette
sfgcSite2DEvaluate2 (sfgcSite2DArbitrary2Form evaluate) plaquette =
  evaluate plaquette

sfgcSite2Dδ₀ :
  SFGCSite2DDiscrete0Form →
  SFGCSite2DDiscrete1Form
sfgcSite2Dδ₀ =
  sfgcSite2DExact1Form

sfgcSite2Dδ₁ :
  SFGCSite2DDiscrete1Form →
  SFGCSite2DDiscrete2Form
sfgcSite2Dδ₁ (sfgcSite2DExact1Form f) =
  sfgcSite2DZero2Form
sfgcSite2Dδ₁ a =
  sfgcSite2DWilsonLoopCurvature a

sfgcSite2DConnectionTo1Form :
  GaugeField →
  SFGCSite2DDiscrete1Form
sfgcSite2DConnectionTo1Form =
  sfgcSite2DConnection1Form

sfgcSite2DP2P3BoundaryOfBoundaryZero :
  (f : SFGCSite2DDiscrete0Form) →
  (base : SFGCSite2D) →
  sfgcSite2DEvaluate2
    (sfgcSite2Dδ₁ (sfgcSite2Dδ₀ f))
    (sfgcSite2DPlaquetteAt base)
    ≡
  SPTI4.φ0
sfgcSite2DP2P3BoundaryOfBoundaryZero f base =
  refl

sfgcSite2DVacuumWilsonLoopFlatness :
  (base : SFGCSite2D) →
  sfgcSite2DEvaluate2
    (sfgcSite2Dδ₁ (sfgcSite2DConnectionTo1Form vacuumGaugeField))
    (sfgcSite2DPlaquetteAt base)
    ≡
  SPTI4.φ0
sfgcSite2DVacuumWilsonLoopFlatness base =
  refl

record SFGCSite2DFieldStrengthBridge : Set where
  field
    curvature2Form :
      SFGCSite2DDiscrete2Form

    wilsonLoopPhase :
      SFGCSite2DPlaquette →
      SPTI4.Phase4

    wilsonLoopPhaseLaw :
      (plaquette : SFGCSite2DPlaquette) →
      wilsonLoopPhase plaquette
        ≡
      sfgcSite2DEvaluate2 curvature2Form plaquette

sfgcSite2DFieldStrengthFromCurvature :
  SFGCSite2DDiscrete2Form →
  SFGCSite2DFieldStrengthBridge
sfgcSite2DFieldStrengthFromCurvature curvature =
  record
    { curvature2Form =
        curvature
    ; wilsonLoopPhase =
        sfgcSite2DEvaluate2 curvature
    ; wilsonLoopPhaseLaw =
        λ plaquette → refl
    }

canonicalSFGCSite2DMinimalP3SemanticExtension :
  SFGCMinimalP3SemanticExtensionAPI
canonicalSFGCSite2DMinimalP3SemanticExtension =
  record
    { ExtendedSFGCSite =
        SFGCSite2D
    ; embedCurrentSite =
        embedCurrentSite2D
    ; p2ShiftAction =
        sfgcSite2DP2ShiftAction
    ; p3ShiftAction =
        sfgcSite2DP3ShiftAction
    ; ExtendedSFGCShiftEdge =
        SFGCSite2DShiftEdge
    ; extendedP2RightLinkAt =
        sfgcSite2DP2RightEdgeAt
    ; extendedP3TransverseLinkAt =
        sfgcSite2DP3TransverseEdgeAt
    ; extendedEdgeSource =
        sfgcSite2DEdgeSource
    ; extendedEdgeTarget =
        sfgcSite2DEdgeTarget
    ; extendedEdgeSourceLaw =
        sfgcSite2DEdgeSourceLaw
    ; extendedP2TargetLaw =
        sfgcSite2DP2TargetLaw
    ; extendedP3TargetLaw =
        sfgcSite2DP3TargetLaw
    ; p2ThenP3 =
        sfgcSite2DP2ThenP3
    ; p3ThenP2 =
        sfgcSite2DP3ThenP2
    ; p2ThenP3Law =
        sfgcSite2DP2ThenP3Law
    ; p3ThenP2Law =
        sfgcSite2DP3ThenP2Law
    ; p2p3EndpointCommutation =
        sfgcSite2DP2P3EndpointCommutation
    ; currentRightCompatibility =
        sfgcSite2DCurrentRightCompatibility
    ; p3NotCurrentRightAction =
        sfgcSite2DP3NotCurrentRightAction
    ; p3NotCurrentLeftActionOnEmbeddedSites =
        sfgcSite2DP3NotCurrentLeftActionOnEmbeddedSites
    ; p3NotIdentityAction =
        sfgcSite2DP3NotIdentityAction
    ; nondegenerateBoundary =
        "SFGCSite2D is a sidecar product carrier over two ShiftPressurePoint axes"
        ∷ "p2ShiftAction advances the first axis by SSL.rightNeighbor and preserves the transverse axis"
        ∷ "p3ShiftAction advances the second axis by SSL.rightNeighbor and preserves the current SFGC axis"
        ∷ "embedCurrentSite places the existing SFGCSite on transverse origin shiftStartPoint"
        ∷ "p2 and p3 endpoint actions commute definitionally because they act on independent axes"
        ∷ "p3 nondegeneracy is witnessed at (shiftStartPoint, shiftStartPoint): p3 reaches (shiftStartPoint, shiftNextPoint), not the p2, left, or identity endpoint"
        ∷ []
    }

record CoreDirectionIndexedSFGCSchema : Set₁ where
  field
    CoreSFGCSite :
      Set

    embedLegacySFGCSite :
      SFGCSite →
      CoreSFGCSite

    coreShiftAction :
      SFGCPrimeDirection →
      CoreSFGCSite →
      CoreSFGCSite

    CoreSFGCShiftEdge :
      SFGCPrimeDirection →
      CoreSFGCSite →
      Set

    coreP2RightLinkAt :
      (site : CoreSFGCSite) →
      CoreSFGCShiftEdge p2Right site

    coreP3TransverseLinkAt :
      (site : CoreSFGCSite) →
      CoreSFGCShiftEdge p3Transverse site

    coreEdgeSource :
      {dir : SFGCPrimeDirection} →
      {site : CoreSFGCSite} →
      CoreSFGCShiftEdge dir site →
      CoreSFGCSite

    coreEdgeTarget :
      {dir : SFGCPrimeDirection} →
      {site : CoreSFGCSite} →
      CoreSFGCShiftEdge dir site →
      CoreSFGCSite

    coreEdgeSourceLaw :
      {dir : SFGCPrimeDirection} →
      (site : CoreSFGCSite) →
      (edge : CoreSFGCShiftEdge dir site) →
      coreEdgeSource edge ≡ site

    coreEdgeTargetLaw :
      {dir : SFGCPrimeDirection} →
      (site : CoreSFGCSite) →
      (edge : CoreSFGCShiftEdge dir site) →
      coreEdgeTarget edge ≡ coreShiftAction dir site

    coreP2ThenP3 :
      CoreSFGCSite →
      CoreSFGCSite

    coreP3ThenP2 :
      CoreSFGCSite →
      CoreSFGCSite

    coreP2ThenP3Law :
      (site : CoreSFGCSite) →
      coreP2ThenP3 site
        ≡
      coreShiftAction p3Transverse (coreShiftAction p2Right site)

    coreP3ThenP2Law :
      (site : CoreSFGCSite) →
      coreP3ThenP2 site
        ≡
      coreShiftAction p2Right (coreShiftAction p3Transverse site)

    coreP2P3EndpointCommutation :
      (site : CoreSFGCSite) →
      coreP2ThenP3 site ≡ coreP3ThenP2 site

    legacyP2RightCompatibility :
      (site : SFGCSite) →
      coreShiftAction p2Right (embedLegacySFGCSite site)
        ≡
      embedLegacySFGCSite (SSL.rightNeighbor site)

    coreSchemaSource :
      SFGCMinimalP3SemanticExtensionAPI

    coreAdoptionBoundary :
      List String

canonicalCoreDirectionIndexedSFGCSchema :
  CoreDirectionIndexedSFGCSchema
canonicalCoreDirectionIndexedSFGCSchema =
  record
    { CoreSFGCSite =
        SFGCSite2D
    ; embedLegacySFGCSite =
        embedCurrentSite2D
    ; coreShiftAction =
        sfgcSite2DShiftAction
    ; CoreSFGCShiftEdge =
        SFGCSite2DShiftEdge
    ; coreP2RightLinkAt =
        sfgcSite2DP2RightEdgeAt
    ; coreP3TransverseLinkAt =
        sfgcSite2DP3TransverseEdgeAt
    ; coreEdgeSource =
        sfgcSite2DEdgeSource
    ; coreEdgeTarget =
        sfgcSite2DEdgeTarget
    ; coreEdgeSourceLaw =
        sfgcSite2DEdgeSourceLaw
    ; coreEdgeTargetLaw =
        λ site →
          λ
            { (sfgcSite2DP2RightEdgeAt .site) →
                refl
            ; (sfgcSite2DP3TransverseEdgeAt .site) →
                refl
            }
    ; coreP2ThenP3 =
        sfgcSite2DP2ThenP3
    ; coreP3ThenP2 =
        sfgcSite2DP3ThenP2
    ; coreP2ThenP3Law =
        sfgcSite2DP2ThenP3Law
    ; coreP3ThenP2Law =
        sfgcSite2DP3ThenP2Law
    ; coreP2P3EndpointCommutation =
        sfgcSite2DP2P3EndpointCommutation
    ; legacyP2RightCompatibility =
        sfgcSite2DCurrentRightCompatibility
    ; coreSchemaSource =
        canonicalSFGCSite2DMinimalP3SemanticExtension
    ; coreAdoptionBoundary =
        "Core-facing direction-indexed SFGC schema adopts SFGCSite2D as the canonical p2/p3 carrier"
        ∷ "The legacy SFGCSite = ShiftPressurePoint and right-only SFGCShiftEdge names are preserved for backwards compatibility"
        ∷ "embedLegacySFGCSite places the old carrier on the p3 origin slice of the adopted core carrier"
        ∷ "CoreSFGCShiftEdge has inhabited p2/right and p3/transverse links over the adopted carrier"
        ∷ "The adopted core schema is sourced from canonicalSFGCSite2DMinimalP3SemanticExtension"
        ∷ []
    }

CanonicalCoreDirectionIndexedSFGCSite :
  Set
CanonicalCoreDirectionIndexedSFGCSite =
  CoreDirectionIndexedSFGCSchema.CoreSFGCSite
    canonicalCoreDirectionIndexedSFGCSchema

CanonicalCoreDirectionIndexedSFGCShiftEdge :
  SFGCPrimeDirection →
  CanonicalCoreDirectionIndexedSFGCSite →
  Set
CanonicalCoreDirectionIndexedSFGCShiftEdge =
  CoreDirectionIndexedSFGCSchema.CoreSFGCShiftEdge
    canonicalCoreDirectionIndexedSFGCSchema

data CoreDirectionIndexedSFGCAdoptionStatus : Set where
  coreDirectionIndexedSFGCSchemaAdopted :
    CoreDirectionIndexedSFGCAdoptionStatus

record SFGCSite2DCoreDirectionIndexedAdoptionReceipt : Set₁ where
  field
    adoptionStatus :
      CoreDirectionIndexedSFGCAdoptionStatus

    adoptedCoreSchema :
      CoreDirectionIndexedSFGCSchema

    adoptedCoreSchemaIsCanonicalSite2D :
      adoptedCoreSchema ≡ canonicalCoreDirectionIndexedSFGCSchema

    adoptedCoreSite :
      Set

    adoptedCoreSiteIsSFGCSite2D :
      adoptedCoreSite ≡ SFGCSite2D

    adoptedCoreShiftEdge :
      SFGCPrimeDirection →
      adoptedCoreSite →
      Set

    adoptedP2RightLinkAt :
      (site : adoptedCoreSite) →
      adoptedCoreShiftEdge p2Right site

    adoptedP3TransverseLinkAt :
      (site : adoptedCoreSite) →
      adoptedCoreShiftEdge p3Transverse site

    legacyCoreNamesPreserved :
      List String

    adoptionReceiptBoundary :
      List String

canonicalSFGCSite2DCoreDirectionIndexedAdoptionReceipt :
  SFGCSite2DCoreDirectionIndexedAdoptionReceipt
canonicalSFGCSite2DCoreDirectionIndexedAdoptionReceipt =
  record
    { adoptionStatus =
        coreDirectionIndexedSFGCSchemaAdopted
    ; adoptedCoreSchema =
        canonicalCoreDirectionIndexedSFGCSchema
    ; adoptedCoreSchemaIsCanonicalSite2D =
        refl
    ; adoptedCoreSite =
        SFGCSite2D
    ; adoptedCoreSiteIsSFGCSite2D =
        refl
    ; adoptedCoreShiftEdge =
        SFGCSite2DShiftEdge
    ; adoptedP2RightLinkAt =
        sfgcSite2DP2RightEdgeAt
    ; adoptedP3TransverseLinkAt =
        sfgcSite2DP3TransverseEdgeAt
    ; legacyCoreNamesPreserved =
        "SFGCSite remains the legacy ShiftPressurePoint alias"
        ∷ "SFGCShiftEdge remains the legacy right-only edge family over SFGCSite"
        ∷ "Direction-indexed core consumers should use CoreDirectionIndexedSFGCSchema"
        ∷ []
    ; adoptionReceiptBoundary =
        "SFGCSite2D is accepted as the canonical core direction-indexed SFGC schema carrier"
        ∷ "This clears the need to add a p3 constructor to the legacy SFGCShiftEdge data type"
        ∷ "Legacy right-only code remains valid; p2/p3 curvature code consumes the adopted schema"
        ∷ []
    }

minimalP3SemanticExtensionAPIName :
  String
minimalP3SemanticExtensionAPIName =
  "SFGCMinimalP3SemanticExtensionAPI"

canonicalSFGCTransverseP3LinkUpstreamAPIRequest :
  SFGCTransverseP3LinkUpstreamAPIRequest
canonicalSFGCTransverseP3LinkUpstreamAPIRequest =
  record
    { siteCarrier =
        SPTI.ShiftPressurePoint
    ; siteCarrierIsCurrentShiftPressurePoint =
        refl
    ; currentConcreteSiteConstructors =
        "shiftStartPoint"
        ∷ "shiftNextPoint"
        ∷ "shiftHeldExitPoint"
        ∷ []
    ; currentSiteEndpointStructure =
        "DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance defines data ShiftPressurePoint with exactly shiftStartPoint, shiftNextPoint, shiftHeldExitPoint"
        ∷ "ShiftPressurePoint is currently a data type, not a record"
        ∷ "No source, target, prime-coordinate, or p3 endpoint projection is exported by ShiftPressurePoint"
        ∷ "DASHI.Physics.ShiftSpatialLaplacian defines rightNeighbor/leftNeighbor only; no p3/transverse action is exported there"
        ∷ "The only endpoint action available to this module is SSL.rightNeighbor through sfgcP2RightEdgeAt"
        ∷ []
    ; rightDirection =
        p2Right
    ; rightDirectionIsP2 =
        refl
    ; transverseDirection =
        p3Transverse
    ; transverseDirectionIsP3 =
        refl
    ; currentRightLinkAt =
        sfgcP2RightEdgeAt
    ; currentRightEndpoint =
        sfgcP2ShiftEdgeTargetLaw
    ; transverseLinkStillUninhabited =
        sfgcP3TransverseShiftEdgeMissing
    ; threePointP3ActionObstruction =
        canonicalSFGCThreePointP3ActionObstruction
    ; requestedUpstreamAPI =
        "A p3-indexed shift action over an explicitly extended SFGC site carrier, not over the current three-point carrier"
        ∷ "transverseP3LinkAt : (site : SFGCSite) -> SFGCShiftEdge p3Transverse site"
        ∷ "p3ShiftAction : SFGCSite -> SFGCSite"
        ∷ "sfgcP3ShiftEdgeTargetLaw : sfgcShiftEdgeTarget (transverseP3LinkAt site) == p3ShiftAction site"
        ∷ "Minimal typed request: SFGCMinimalP3SemanticExtensionAPI"
        ∷ "The extension must expose ExtendedSFGCSite, p2ShiftAction, p3ShiftAction, p2/p3 edge constructors, source/target laws, and p2ThenP3/p3ThenP2 commutation"
        ∷ "p3ShiftAction must be supplied as a function/law over SFGCSite, not inferred from non-existent ShiftPressurePoint record fields"
        ∷ "p2ThenP3/p3ThenP2 endpoint laws over the same SFGCSite carrier"
        ∷ "a nondegeneracy proof that p3ShiftAction is not the reflected/right-neighbor action"
        ∷ "nondegeneracy must also exclude identity and collapse-only actions on the current three-point carrier"
        ∷ []
    ; failClosedReason =
        "The current SFGCSite is the three-constructor ShiftPressurePoint process carrier"
        ∷ "Definition-site evidence: ShiftPressurePoint has only shiftStartPoint, shiftNextPoint, and shiftHeldExitPoint constructors"
        ∷ "ShiftPressurePoint exposes no endpoint record fields to project a p3 link"
        ∷ "The only concrete exported SFGCShiftEdge constructor is sfgcP2RightEdgeAt"
        ∷ "Pattern matching on SFGCShiftEdge has no p3Transverse constructor, so sfgcP3TransverseShiftEdgeMissing is inhabited by the empty pattern"
        ∷ "The only concrete endpoint action exposed here is SSL.rightNeighbor"
        ∷ "Reusing rightNeighbor as p3Transverse would collapse the p2/p3 plaquette"
        ∷ []
    }

leftGaugePhase :
  GaugeField →
  SPTI.ShiftPressurePoint →
  SPTI4.Phase4
leftGaugePhase A s =
  SFGS.phaseInv4 (A (SSL.leftNeighbor s))

rightGaugePhase :
  GaugeField →
  SPTI.ShiftPressurePoint →
  SPTI4.Phase4
rightGaugePhase A s = A s

covariantLaplacian :
  GaugeField →
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
covariantLaplacian A ψ s =
  SDWS.waveAdd
    (SFGS.phaseAct (leftGaugePhase A s) (ψ (SSL.leftNeighbor s)))
    (SDWS.waveAdd
      (SFGS.phaseAct (rightGaugePhase A s) (ψ (SSL.rightNeighbor s)))
      (SDWS.scaleWave (-[1+ 1 ]) (ψ s)))

waveNeg : SDWS.DiscreteWave → SDWS.DiscreteWave
waveNeg ψ =
  SDWS.scaleWave (-[1+ 0 ]) ψ

gaugeHamiltonian :
  GaugeField →
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
gaugeHamiltonian A ψ s =
  waveNeg (covariantLaplacian A ψ s)

gaugeSchrodingerStep :
  GaugeField →
  SSL.ShiftWaveField →
  SPTI.ShiftPressurePoint →
  SDWS.DiscreteWave
gaugeSchrodingerStep A ψ s =
  SDWS.waveAdd
    (ψ s)
    (SDWS.mulI (gaugeHamiltonian A ψ s))

gaugeGlobalUpdate :
  GaugeField →
  SSL.ShiftWaveField →
  SSL.ShiftWaveField
gaugeGlobalUpdate A ψ s =
  gaugeSchrodingerStep A ψ s

transformGauge :
  SFGS.GaugeTransform →
  GaugeField →
  GaugeField
transformGauge g A s =
  SFGS.phaseAdd4
    (SFGS.phaseInv4 (g (SSL.rightNeighbor s)))
    (SFGS.phaseAdd4 (A s) (g s))

VacuumGaugeCompatibility : Set
VacuumGaugeCompatibility =
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  covariantLaplacian vacuumGaugeField ψ s
    ≡
  SSL.shiftSpatialLaplacian ψ s

vacuumGaugeCompatibility : VacuumGaugeCompatibility
vacuumGaugeCompatibility ψ SPTI.shiftStartPoint = refl
vacuumGaugeCompatibility ψ SPTI.shiftNextPoint = refl
vacuumGaugeCompatibility ψ SPTI.shiftHeldExitPoint = refl

ConstantGaugePreservesVacuum : Set
ConstantGaugePreservesVacuum =
  (φ : SPTI4.Phase4) →
  (s : SPTI.ShiftPressurePoint) →
  transformGauge (SFGS.constantGaugeTransform φ) vacuumGaugeField s
    ≡
  vacuumGaugeField s

constantGaugePreservesVacuum : ConstantGaugePreservesVacuum
constantGaugePreservesVacuum SPTI4.φ0 s = refl
constantGaugePreservesVacuum SPTI4.φ1 SPTI.shiftStartPoint = refl
constantGaugePreservesVacuum SPTI4.φ1 SPTI.shiftNextPoint = refl
constantGaugePreservesVacuum SPTI4.φ1 SPTI.shiftHeldExitPoint = refl
constantGaugePreservesVacuum SPTI4.φ2 SPTI.shiftStartPoint = refl
constantGaugePreservesVacuum SPTI4.φ2 SPTI.shiftNextPoint = refl
constantGaugePreservesVacuum SPTI4.φ2 SPTI.shiftHeldExitPoint = refl
constantGaugePreservesVacuum SPTI4.φ3 SPTI.shiftStartPoint = refl
constantGaugePreservesVacuum SPTI4.φ3 SPTI.shiftNextPoint = refl
constantGaugePreservesVacuum SPTI4.φ3 SPTI.shiftHeldExitPoint = refl

ConstantPhaseVacuumCovarianceTarget : Set
ConstantPhaseVacuumCovarianceTarget =
  (φ : SPTI4.Phase4) →
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  covariantLaplacian
    (transformGauge (SFGS.constantGaugeTransform φ) vacuumGaugeField)
    (SFGS.transformMatter (SFGS.constantGaugeTransform φ) ψ)
    s
    ≡
  SFGS.phaseAct φ (covariantLaplacian vacuumGaugeField ψ s)

LocalGaugeCovarianceTarget : Set
LocalGaugeCovarianceTarget =
  (g : SFGS.GaugeTransform) →
  (A : GaugeField) →
  (ψ : SSL.ShiftWaveField) →
  (s : SPTI.ShiftPressurePoint) →
  covariantLaplacian
    (transformGauge g A)
    (SFGS.transformMatter g ψ)
    s
    ≡
  SFGS.phaseAct (g s) (covariantLaplacian A ψ s)

record ShiftFiniteGaugeCoupling : Set₁ where
  field
    MatterField : Set
    StaticGaugeField : Set
    gaugeVacuum : StaticGaugeField
    gaugePotential :
      SPTI.ShiftPressurePoint → StaticGaugeField → SPTI4.Phase4
    gaugeAction :
      SFGS.GaugeTransform → StaticGaugeField → StaticGaugeField
    covariantOperator :
      StaticGaugeField →
      MatterField →
      SPTI.ShiftPressurePoint →
      SDWS.DiscreteWave
    covariantUpdate :
      StaticGaugeField → MatterField → MatterField
    vacuumCompatibilityLaw : VacuumGaugeCompatibility
    constantGaugeVacuumPreservation : ConstantGaugePreservesVacuum
    constantPhaseCovarianceTarget : Set
    localGaugeCovarianceTarget : Set
    nonClaimBoundary : List String

shiftFiniteGaugeCoupling : ShiftFiniteGaugeCoupling
shiftFiniteGaugeCoupling =
  record
    { MatterField = SSL.ShiftWaveField
    ; StaticGaugeField = GaugeField
    ; gaugeVacuum = vacuumGaugeField
    ; gaugePotential = λ s A → A s
    ; gaugeAction = transformGauge
    ; covariantOperator = covariantLaplacian
    ; covariantUpdate = gaugeGlobalUpdate
    ; vacuumCompatibilityLaw = vacuumGaugeCompatibility
    ; constantGaugeVacuumPreservation = constantGaugePreservesVacuum
    ; constantPhaseCovarianceTarget = ConstantPhaseVacuumCovarianceTarget
    ; localGaugeCovarianceTarget = LocalGaugeCovarianceTarget
    ; nonClaimBoundary =
        "Finite matter-plus-static-gauge package only"
        ∷ "Gauge field is a bounded Phase4 link assignment on the current coarse carrier"
        ∷ "Covariant Laplacian is a nearest-neighbor transport operator with reflected boundaries"
        ∷ "Full local and constant-phase covariance are exposed as target law surfaces, not solved in this lane"
        ∷ "Only vacuum compatibility and constant-gauge preservation of the vacuum link field are witnessed explicitly"
        ∷ "No dynamic gauge field, continuum connection, Yang-Mills, or full U(1) claim is implied"
        ∷ []
    }
