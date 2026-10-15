module DASHI.Physics.Closure.MonsterGravityAuthorityAndDimensionExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- Primary authority anchors.  arXiv links are used directly here rather than
-- secondary discovery pages.  Citation records provenance and claim ceiling;
-- it does not import a theorem into DASHI.
------------------------------------------------------------------------

witten2007Source : Source.AttributedSource
witten2007Source =
  Source.mkNoDOISource
    "Edward Witten"
    "Three-Dimensional Gravity Revisited"
    "arXiv:0706.3359"
    "2007"
    "https://arxiv.org/abs/0706.3359"
    Source.academicArticleSource
    "authority anchor for a candidate AdS3 pure-gravity/extremal holomorphic CFT route whose minimal case is very likely the Monster theory; not a 3+1D observed-universe theorem"
    Source.publicAttribution

marraniRiosChester2020Source : Source.AttributedSource
marraniRiosChester2020Source =
  Source.mkNoDOISource
    "Alessio Marrani; Michael Rios; David Chester"
    "Monstrous M-theory"
    "arXiv:2008.06742"
    "2020"
    "https://arxiv.org/abs/2008.06742"
    Source.academicArticleSource
    "authority anchor for a 26+1-dimensional gravity construction whose 25+1 reduction carries a 1 plus 196883 Monster-action spectrum; not observed 3+1D evidence"
    Source.publicAttribution

jacobson1995Source : Source.AttributedSource
jacobson1995Source =
  Source.mkNoDOISource
    "Ted Jacobson"
    "Thermodynamics of Spacetime: The Einstein Equation of State"
    "arXiv:gr-qc/9504004"
    "1995"
    "https://arxiv.org/abs/gr-qc/9504004"
    Source.academicArticleSource
    "authority anchor for deriving the Einstein equation from local Rindler causal horizons, entropy-area proportionality, heat flux and Unruh temperature under the paper's assumptions"
    Source.publicAttribution

jacobson2015Source : Source.AttributedSource
jacobson2015Source =
  Source.mkNoDOISource
    "Ted Jacobson"
    "Entanglement Equilibrium and the Einstein Equation"
    "arXiv:1505.04753"
    "2015"
    "https://arxiv.org/abs/1505.04753"
    Source.academicArticleSource
    "authority anchor for first-order entanglement-equilibrium / semiclassical Einstein-equation reasoning in small geodesic balls under stated assumptions"
    Source.publicAttribution

padmanabhan2010Source : Source.AttributedSource
padmanabhan2010Source =
  Source.mkNoDOISource
    "T. Padmanabhan"
    "Entropy density of spacetime and the Navier-Stokes fluid dynamics of null surfaces"
    "arXiv:1012.0119"
    "2010"
    "https://arxiv.org/abs/1012.0119"
    Source.academicArticleSource
    "authority anchor for a null-surface spacetime-entropy-density extremisation route and its projected gravitational/Navier-Stokes structure; not an arbitrary scalar-density-equals-gravity theorem"
    Source.publicAttribution

monsterEntropyGravitySourceAtlas : Source.AttributedSourceAtlas
monsterEntropyGravitySourceAtlas =
  Source.mkSourceAtlas
    "Monster / entropy / gravity authority atlas"
    "DASHI.Physics.Closure.MonsterGravityAuthorityAndDimensionExact"
    (witten2007Source
      ∷ marraniRiosChester2020Source
      ∷ jacobson1995Source
      ∷ jacobson2015Source
      ∷ padmanabhan2010Source
      ∷ [])
    "claim-relative primary authority for distinct dimensional Monster/gravity and entropy/gravity routes; no source is promoted beyond its own construction and assumptions"

------------------------------------------------------------------------
-- Dimensional route audit.
------------------------------------------------------------------------

data GravityRouteKind : Set where
  monsterAdS3Candidate : GravityRouteKind
  monstrousMTheoryHighDimensional : GravityRouteKind
  jacobsonLocalHorizonThermodynamic : GravityRouteKind
  jacobsonEntanglementEquilibrium : GravityRouteKind
  padmanabhanNullEntropyDensity : GravityRouteKind
  targetObservedThreePlusOne : GravityRouteKind

record GravityRouteDescriptor : Set where
  constructor gravityRouteDescriptor
  field
    routeKind : GravityRouteKind
    spacetimeDimension : Nat
    reducedDimension : Nat
    primarySource : Source.AttributedSource
    monsterActionClaimed : Bool
    einsteinDynamicsRouteClaimed : Bool
    observedThreePlusOneIdentified : Bool
    routeCeiling : String

open GravityRouteDescriptor public

wittenAdS3MonsterRoute : GravityRouteDescriptor
wittenAdS3MonsterRoute =
  gravityRouteDescriptor
    monsterAdS3Candidate
    3
    3
    witten2007Source
    true
    true
    false
    "candidate three-dimensional negative-cosmological-constant gravity / extremal holomorphic CFT route; minimal case likely Monster CFT; no observed 3+1D identification"

monstrousMTheoryRoute : GravityRouteDescriptor
monstrousMTheoryRoute =
  gravityRouteDescriptor
    monstrousMTheoryHighDimensional
    27
    26
    marraniRiosChester2020Source
    true
    true
    false
    "26+1 gravity construction reduced to 25+1 with 1 plus 196883 Monster-action spectrum; not a compactification to observed 3+1D physics"

jacobson1995LocalHorizonRoute : GravityRouteDescriptor
jacobson1995LocalHorizonRoute =
  gravityRouteDescriptor
    jacobsonLocalHorizonThermodynamic
    4
    4
    jacobson1995Source
    false
    true
    true
    "four-dimensional local-horizon thermodynamic Einstein-equation route under entropy-area, heat-flux and Unruh-temperature assumptions; contains no Monster identification"

jacobson2015EntanglementRoute : GravityRouteDescriptor
jacobson2015EntanglementRoute =
  gravityRouteDescriptor
    jacobsonEntanglementEquilibrium
    4
    4
    jacobson2015Source
    false
    true
    true
    "four-dimensional semiclassical entanglement-equilibrium route under small-ball and matter assumptions; contains no Monster identification"

padmanabhanNullEntropyRoute : GravityRouteDescriptor
padmanabhanNullEntropyRoute =
  gravityRouteDescriptor
    padmanabhanNullEntropyDensity
    4
    4
    padmanabhan2010Source
    false
    true
    true
    "four-dimensional null-surface entropy-density extremisation route; null/tensor/geometric structure is essential and is not supplied by an arbitrary scalar count"

record DimensionalPromotionBoundary : Set where
  constructor dimensionalPromotionBoundary
  field
    ads3MonsterImpliesObserved4DMonster : Bool
    ads3MonsterImpliesObserved4DMonsterIsFalse :
      ads3MonsterImpliesObserved4DMonster ≡ false

    monstrousMTheoryImpliesObserved4DMonster : Bool
    monstrousMTheoryImpliesObserved4DMonsterIsFalse :
      monstrousMTheoryImpliesObserved4DMonster ≡ false

    entropyGravityRouteImpliesMonster : Bool
    entropyGravityRouteImpliesMonsterIsFalse :
      entropyGravityRouteImpliesMonster ≡ false

    common196883DimensionIsPhysicalIntertwiner : Bool
    common196883DimensionIsPhysicalIntertwinerIsFalse :
      common196883DimensionIsPhysicalIntertwiner ≡ false

canonicalDimensionalPromotionBoundary : DimensionalPromotionBoundary
canonicalDimensionalPromotionBoundary =
  dimensionalPromotionBoundary
    false refl
    false refl
    false refl
    false refl
