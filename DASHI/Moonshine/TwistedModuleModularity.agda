module DASHI.Moonshine.TwistedModuleModularity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Moonshine.VertexOperatorAlgebraCore as VOA
import DASHI.Moonshine.VNaturalOrbifoldConstruction as VN
import DASHI.Moonshine.GradedRepresentation as GR

record GroupWithInverse (G : Set) : Setω where
  field
    group : GR.Group G
    inverse : G → G
    leftInverse : ∀ g → GR.Group._∙_ group (inverse g) g ≡ GR.Group.identity group
    rightInverse : ∀ g → GR.Group._∙_ group g (inverse g) ≡ GR.Group.identity group

open GroupWithInverse public

record CommutingPair
  {G : Set}
  (groupInv : GroupWithInverse G) : Set where
  field
    g h : G
    commute :
      GR.Group._∙_ (GroupWithInverse.group groupInv) g h
      ≡
      GR.Group._∙_ (GroupWithInverse.group groupInv) h g

open CommutingPair public

record TwistedSectorFamily
  {G : Set}
  (groupInv : GroupWithInverse G)
  (construction : VN.VNaturalConstruction) : Setω where
  field
    sector : G → Set
    untwistedSectorAgreesWithVnatural : Set
    twistedVertexAction :
      ∀ g →
      VOA.GradedModule.Carrier
        (VOA.VertexOperatorAlgebra.gradedModule
          (VN.VNaturalConstruction.Vnatural construction)) →
      sector g → sector g
    lowerTruncation : Set
    twistedJacobi : Set
    conjugacyTransport : Set

open TwistedSectorFamily public

record TwistedTraceSystem
  {G K : Set}
  (groupInv : GroupWithInverse G)
  (construction : VN.VNaturalConstruction)
  (sectors : TwistedSectorFamily groupInv construction) : Setω where
  field
    ExactSeries : Set
    traceSeries :
      (pair : CommutingPair groupInv) → ExactSeries
    coefficientRing : Set
    traceRealizedBySector : Set
    vacuumNormalization : Set
    conjugacyInvariant : Set

open TwistedTraceSystem public

record SL2ZAction : Setω where
  field
    Matrix : Set
    identity : Matrix
    _∙_ : Matrix → Matrix → Matrix
    S T : Matrix
    inverse : Matrix → Matrix
    associativity : Set
    identityLaw : Set
    inverseLaw : Set
    presentationS4 : Set
    presentationST3 : Set

open SL2ZAction public

record TwistedModularity
  {G K : Set}
  (groupInv : GroupWithInverse G)
  (construction : VN.VNaturalConstruction)
  (sectors : TwistedSectorFamily groupInv construction)
  (traces : TwistedTraceSystem groupInv construction sectors)
  (modularGroup : SL2ZAction) : Setω where
  field
    transformPair :
      SL2ZAction.Matrix modularGroup →
      CommutingPair groupInv →
      CommutingPair groupInv
    slash :
      SL2ZAction.Matrix modularGroup →
      TwistedTraceSystem.ExactSeries traces →
      TwistedTraceSystem.ExactSeries traces
    STransformsPair : Set
    TTransformsPair : Set
    covariance :
      ∀ gamma pair →
      slash gamma (TwistedTraceSystem.traceSeries traces pair)
      ≡
      TwistedTraceSystem.traceSeries traces (transformPair gamma pair)
    projectiveMultiplier : Set
    finiteImageMultiplier : Set

open TwistedModularity public

record RationalityCofinitenessInput
  (construction : VN.VNaturalConstruction) : Setω where
  field
    rational : Set
    C2Cofinite : Set
    selfContragradient : Set
    finiteIrreducibleModuleSet : Set
    convergentCharacters : Set

open RationalityCofinitenessInput public

record VNaturalModularityPackage
  {G K : Set}
  (groupInv : GroupWithInverse G)
  (construction : VN.VNaturalConstruction) : Setω where
  field
    sectors : TwistedSectorFamily groupInv construction
    traces : TwistedTraceSystem groupInv construction sectors
    modularGroup : SL2ZAction
    modularity : TwistedModularity groupInv construction sectors traces modularGroup
    finitenessInput : RationalityCofinitenessInput construction

open VNaturalModularityPackage public
