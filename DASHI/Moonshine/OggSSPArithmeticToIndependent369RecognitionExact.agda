module DASHI.Moonshine.OggSSPArithmeticToIndependent369RecognitionExact where

------------------------------------------------------------------------
-- ARITHMETIC -> RESIDUAL -> INDEPENDENT BASE369 RECOGNITION
--
-- DASHI CONTRIBUTION
--
-- The canonical forward owner already requests:
--
--   G_p^arith -> G_p^residual
--
-- The new independent target recognitions prove:
--
--   G_3^residual -> G_3^369(SSPTrit)
--   G_2^residual(retained) -> G_2^369(OrientationPolarity x NineOrbit)
--
-- Recognition composition therefore makes the direct arithmetic->independent
-- Base369 theorem automatic once the arithmetic source/socket and first-leg
-- recognition are actually inhabited.
--
-- No arithmetic source is constructed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as Provenance
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Moonshine.OggSSPSmallCharacteristicArithmeticSourceSocketExact as SourceSocket
import DASHI.Moonshine.OggSSPArithmeticTo369RecognitionExact as Forward
import DASHI.Moonshine.OggSSPP3Base369RecognitionExact as P3Bridge
import DASHI.Moonshine.OggSSPP2Base369RecognitionForkExact as P2Bridge
import DASHI.Moonshine.Base369P3ConstantTernaryActionGroupoidExact as P3Target
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as P2Target
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Residual
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. p=3 direct recognition by composition.
------------------------------------------------------------------------

p3IndependentFunctor :
  {source : SourceSocket.P3MarkedFrobeniusSource} ->
  Forward.P3ArithmeticTo369Recognition source ->
  Recognition.ActionRecognitionFunctor
    (SourceSocket.action source)
    P3Target.p3C2Action
p3IndependentFunctor recognition =
  Recognition.composeActionRecognition
    (Forward.P3ArithmeticTo369Recognition.functor recognition)
    P3Bridge.p3ActionRecognition

p3IndependentFullRecognition :
  {source : SourceSocket.P3MarkedFrobeniusSource} ->
  (recognition : Forward.P3ArithmeticTo369Recognition source) ->
  Recognition.OrbitStabilizerRecognition
    (p3IndependentFunctor recognition)
    (SourceSocket.orbits source)
    P3Target.p3OrbitPresentation
p3IndependentFullRecognition recognition =
  Recognition.composeOrbitStabilizerRecognition
    (Forward.P3ArithmeticTo369Recognition.fullRecognition recognition)
    P3Bridge.p3FullRecognition

p3IndependentOrbitRecognition :
  {source : SourceSocket.P3MarkedFrobeniusSource} ->
  (recognition : Forward.P3ArithmeticTo369Recognition source) ->
  Recognition.OrbitRecognition
    (p3IndependentFunctor recognition)
    (SourceSocket.orbits source)
    P3Target.p3OrbitPresentation
p3IndependentOrbitRecognition recognition =
  Recognition.orbitRecognition
    (p3IndependentFullRecognition recognition)

------------------------------------------------------------------------
-- 2. p=2 retained-orientation direct recognition by composition.
------------------------------------------------------------------------

p2IndependentFunctor :
  {source : SourceSocket.P2MarkedArithmeticSource} ->
  Forward.P2ArithmeticTo369Recognition source ->
  Recognition.ActionRecognitionFunctor
    (SourceSocket.action source)
    P2Target.p2RetainedAction
p2IndependentFunctor recognition =
  Recognition.composeActionRecognition
    (Forward.P2ArithmeticTo369Recognition.functor recognition)
    P2Bridge.p2RetainedActionRecognition

p2IndependentFullRecognition :
  {source : SourceSocket.P2MarkedArithmeticSource} ->
  (recognition : Forward.P2ArithmeticTo369Recognition source) ->
  Recognition.OrbitStabilizerRecognition
    (p2IndependentFunctor recognition)
    (SourceSocket.orbits source)
    P2Target.p2RetainedOrbitPresentation
p2IndependentFullRecognition recognition =
  Recognition.composeOrbitStabilizerRecognition
    (Forward.P2ArithmeticTo369Recognition.fullRecognition recognition)
    P2Bridge.p2RetainedFullRecognition

p2IndependentOrbitRecognition :
  {source : SourceSocket.P2MarkedArithmeticSource} ->
  (recognition : Forward.P2ArithmeticTo369Recognition source) ->
  Recognition.OrbitRecognition
    (p2IndependentFunctor recognition)
    (SourceSocket.orbits source)
    P2Target.p2RetainedOrbitPresentation
p2IndependentOrbitRecognition recognition =
  Recognition.orbitRecognition
    (p2IndependentFullRecognition recognition)

------------------------------------------------------------------------
-- 3. Provenance-lift sockets.
--
-- The current arithmetic source sockets do not expose a provenance coordinate.
-- Rather than changing their meaning retroactively, we add a wrapper requiring
-- a provenance-bearing first leg.  The second leg is already proved.
------------------------------------------------------------------------

record P3ArithmeticProvenanceFirstLeg
    (source : SourceSocket.P3MarkedFrobeniusSource) : Set₂ where
  field
    ArithmeticProvenance : Set
    arithmeticProvenance :
      SourceSocket.MarkedState source ->
      ArithmeticProvenance

    firstLegAction :
      Provenance.ProvenancePreservingActionRecognition
        (SourceSocket.action source)
        Residual.constantC2Action
        arithmeticProvenance
        P3Bridge.sourceProvenance

    firstLegOrbit :
      Provenance.ProvenancePreservingOrbitRecognition
        firstLegAction
        (SourceSocket.orbits source)
        Residual.constantTernaryOrbitPresentation

open P3ArithmeticProvenanceFirstLeg public

p3IndependentProvenanceRecognition :
  {source : SourceSocket.P3MarkedFrobeniusSource} ->
  (first : P3ArithmeticProvenanceFirstLeg source) ->
  Provenance.ProvenancePreservingOrbitRecognition
    (Provenance.composeProvenancePreservingActionRecognition
      (firstLegAction first)
      P3Bridge.p3ProvenanceActionRecognition)
    (SourceSocket.orbits source)
    P3Target.p3OrbitPresentation
p3IndependentProvenanceRecognition first =
  Provenance.composeProvenancePreservingOrbitRecognition
    (firstLegOrbit first)
    P3Bridge.p3ProvenanceOrbitRecognition

record P2ArithmeticProvenanceFirstLeg
    (source : SourceSocket.P2MarkedArithmeticSource) : Set₂ where
  field
    ArithmeticProvenance : Set
    arithmeticProvenance :
      SourceSocket.MarkedState source ->
      ArithmeticProvenance

    firstLegAction :
      Provenance.ProvenancePreservingActionRecognition
        (SourceSocket.action source)
        Residual.p2DiscreteAction
        arithmeticProvenance
        P2Bridge.sourceOrientationProvenance

    firstLegOrbit :
      Provenance.ProvenancePreservingOrbitRecognition
        firstLegAction
        (SourceSocket.orbits source)
        Residual.p2DiscreteOrbitPresentation

open P2ArithmeticProvenanceFirstLeg public

p2IndependentProvenanceRecognition :
  {source : SourceSocket.P2MarkedArithmeticSource} ->
  (first : P2ArithmeticProvenanceFirstLeg source) ->
  Provenance.ProvenancePreservingOrbitRecognition
    (Provenance.composeProvenancePreservingActionRecognition
      (firstLegAction first)
      P2Bridge.retainedProvenanceRecognition)
    (SourceSocket.orbits source)
    P2Target.p2RetainedOrbitPresentation
p2IndependentProvenanceRecognition first =
  Provenance.composeProvenancePreservingOrbitRecognition
    (firstLegOrbit first)
    P2Bridge.retainedProvenanceOrbitRecognition

------------------------------------------------------------------------
-- 4. Promotion boundary.
------------------------------------------------------------------------

data CompositionConstructsMissingArithmeticSource : Set where
data Independent369TargetDecidesP2ArithmeticSemantics : Set where
data ProvenanceSocketManufacturesArithmeticHistory : Set where

compositionDoesNotConstructMissingArithmeticSource :
  CompositionConstructsMissingArithmeticSource -> ⊥
compositionDoesNotConstructMissingArithmeticSource ()

independent369TargetDoesNotDecideP2ArithmeticSemantics :
  Independent369TargetDecidesP2ArithmeticSemantics -> ⊥
independent369TargetDoesNotDecideP2ArithmeticSemantics ()

provenanceSocketDoesNotManufactureArithmeticHistory :
  ProvenanceSocketManufacturesArithmeticHistory -> ⊥
provenanceSocketDoesNotManufactureArithmeticHistory ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryNewExtension

record ArithmeticToIndependent369Boundary : Set where
  constructor arithmetic-to-independent369-boundary
  field
    recognitionCompositionOwned : Bool
    p3ResidualToIndependent369RecognitionPaid : Bool
    p2RetainedResidualToIndependent369RecognitionPaid : Bool
    futureP3ArithmeticRecognitionComposesDirectly : Bool
    futureP2ArithmeticRecognitionComposesDirectly : Bool
    provenanceCompositionOwned : Bool
    arithmeticSourceProvenanceStillMustBeSupplied : Bool
    missingArithmeticSourceConstructedHere : Bool
    p2ArithmeticSemanticsDecidedHere : Bool

canonicalArithmeticToIndependent369Boundary :
  ArithmeticToIndependent369Boundary
canonicalArithmeticToIndependent369Boundary =
  arithmetic-to-independent369-boundary
    true true true true true true true false false
