module DASHI.Moonshine.OggSSPP3DeligneRapoportLocalStrataRecognitionExact where

------------------------------------------------------------------------
-- p=3 DELIGNE--RAPOPORT LOCAL-STRATA RECOGNITION
--
-- CLASSICAL INPUT
--
-- Deligne--Rapoport: the special fibre of X0(p) has two components meeting
-- along the supersingular locus.  The two p-isogeny branches are Frobenius and
-- Verschiebung.  At p=3 there is one coarse supersingular j-class, defined
-- over F3, so the local incidence object has exactly three strata:
--
--   Frobenius branch, supersingular node, Verschiebung branch.
--
-- The Atkin--Lehner/duality involution exchanges the two branches and fixes
-- the supersingular node.
--
-- DASHI CONTRIBUTION
--
-- We formalise that classical local incidence C2-set and prove an exact
-- two-sided recognition with the existing three-state KernelTrit carrier.
--
-- This is a classical realization of the ABSTRACT THREE-STATE C2-SET.
-- It does not identify an F9 extension coordinate with a geometric local
-- parameter, nor does it claim three distinct supersingular curves.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.TriadicKernelLiftQuotientExact as Kernel
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2
import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Residual
import DASHI.Moonshine.OggSSPSmallCharacteristicClassicalSourceAtlasExact as Classical
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Classical local incidence carrier.
------------------------------------------------------------------------

data P3LocalStratum : Set where
  frobeniusBranch : P3LocalStratum
  supersingularNode : P3LocalStratum
  verschiebungBranch : P3LocalStratum

dualLocalStratum :
  P3LocalStratum ->
  P3LocalStratum
dualLocalStratum frobeniusBranch = verschiebungBranch
dualLocalStratum supersingularNode = supersingularNode
dualLocalStratum verschiebungBranch = frobeniusBranch

dualLocalStratumInvolutive :
  (stratum : P3LocalStratum) ->
  dualLocalStratum (dualLocalStratum stratum) ≡ stratum
dualLocalStratumInvolutive frobeniusBranch = refl
dualLocalStratumInvolutive supersingularNode = refl
dualLocalStratumInvolutive verschiebungBranch = refl

actLocalC2 :
  C2.C2 ->
  P3LocalStratum ->
  P3LocalStratum
actLocalC2 C2.identity stratum = stratum
actLocalC2 C2.flip stratum = dualLocalStratum stratum

localIdentityActs :
  (stratum : P3LocalStratum) ->
  actLocalC2 C2.identity stratum ≡ stratum
localIdentityActs stratum = refl

localCombineActs :
  (g h : C2.C2) ->
  (stratum : P3LocalStratum) ->
  actLocalC2 (C2.combineC2 g h) stratum
  ≡
  actLocalC2 g (actLocalC2 h stratum)
localCombineActs C2.identity h stratum = refl
localCombineActs C2.flip C2.identity stratum = refl
localCombineActs C2.flip C2.flip stratum =
  sym (dualLocalStratumInvolutive stratum)

localInverseLeft :
  (g : C2.C2) ->
  (stratum : P3LocalStratum) ->
  actLocalC2 (C2.inverseC2 g) (actLocalC2 g stratum) ≡ stratum
localInverseLeft C2.identity stratum = refl
localInverseLeft C2.flip stratum = dualLocalStratumInvolutive stratum

localInverseRight :
  (g : C2.C2) ->
  (stratum : P3LocalStratum) ->
  actLocalC2 g (actLocalC2 (C2.inverseC2 g) stratum) ≡ stratum
localInverseRight C2.identity stratum = refl
localInverseRight C2.flip stratum = dualLocalStratumInvolutive stratum

p3LocalStrataAction :
  Action.InvertibleSymmetryAction P3LocalStratum C2.C2
p3LocalStrataAction =
  Action.invertibleSymmetryAction
    C2.identity
    C2.combineC2
    C2.inverseC2
    actLocalC2
    localIdentityActs
    localCombineActs
    localInverseLeft
    localInverseRight

------------------------------------------------------------------------
-- 2. Exact two-orbit presentation.
------------------------------------------------------------------------

data P3LocalOrbit : Set where
  nodeOrbit : P3LocalOrbit
  branchOrbit : P3LocalOrbit

localOrbitOf :
  P3LocalStratum ->
  P3LocalOrbit
localOrbitOf supersingularNode = nodeOrbit
localOrbitOf frobeniusBranch = branchOrbit
localOrbitOf verschiebungBranch = branchOrbit

localRepresentative :
  P3LocalOrbit ->
  P3LocalStratum
localRepresentative nodeOrbit = supersingularNode
localRepresentative branchOrbit = verschiebungBranch

localOrbitInvariant :
  (g : C2.C2) ->
  (stratum : P3LocalStratum) ->
  localOrbitOf (actLocalC2 g stratum)
  ≡
  localOrbitOf stratum
localOrbitInvariant C2.identity stratum = refl
localOrbitInvariant C2.flip frobeniusBranch = refl
localOrbitInvariant C2.flip supersingularNode = refl
localOrbitInvariant C2.flip verschiebungBranch = refl

localRepresentativeInOrbit :
  (orbit : P3LocalOrbit) ->
  localOrbitOf (localRepresentative orbit) ≡ orbit
localRepresentativeInOrbit nodeOrbit = refl
localRepresentativeInOrbit branchOrbit = refl

localTransporter :
  P3LocalStratum ->
  C2.C2
localTransporter frobeniusBranch = C2.flip
localTransporter supersingularNode = C2.identity
localTransporter verschiebungBranch = C2.identity

localTransporterHits :
  (stratum : P3LocalStratum) ->
  actLocalC2
    (localTransporter stratum)
    (localRepresentative (localOrbitOf stratum))
  ≡ stratum
localTransporterHits frobeniusBranch = refl
localTransporterHits supersingularNode = refl
localTransporterHits verschiebungBranch = refl

p3LocalStrataOrbitPresentation :
  Orbit.OrbitPresentation p3LocalStrataAction
p3LocalStrataOrbitPresentation =
  Orbit.orbitPresentation
    P3LocalOrbit
    localOrbitOf
    localRepresentative
    localOrbitInvariant
    localRepresentativeInOrbit
    localTransporter
    localTransporterHits

------------------------------------------------------------------------
-- 3. Exact rechart to KernelTrit.
------------------------------------------------------------------------

localToKernel :
  P3LocalStratum ->
  Kernel.KernelTrit
localToKernel frobeniusBranch = Kernel.negativeTrit
localToKernel supersingularNode = Kernel.zeroTrit
localToKernel verschiebungBranch = Kernel.positiveTrit

kernelToLocal :
  Kernel.KernelTrit ->
  P3LocalStratum
kernelToLocal Kernel.negativeTrit = frobeniusBranch
kernelToLocal Kernel.zeroTrit = supersingularNode
kernelToLocal Kernel.positiveTrit = verschiebungBranch

localRoundTrip :
  (stratum : P3LocalStratum) ->
  kernelToLocal (localToKernel stratum) ≡ stratum
localRoundTrip frobeniusBranch = refl
localRoundTrip supersingularNode = refl
localRoundTrip verschiebungBranch = refl

kernelRoundTrip :
  (state : Kernel.KernelTrit) ->
  localToKernel (kernelToLocal state) ≡ state
kernelRoundTrip Kernel.negativeTrit = refl
kernelRoundTrip Kernel.zeroTrit = refl
kernelRoundTrip Kernel.positiveTrit = refl

localKernelEquivariant :
  (g : C2.C2) ->
  (stratum : P3LocalStratum) ->
  localToKernel (actLocalC2 g stratum)
  ≡
  Residual.actConstantC2 g (localToKernel stratum)
localKernelEquivariant C2.identity stratum = refl
localKernelEquivariant C2.flip frobeniusBranch = refl
localKernelEquivariant C2.flip supersingularNode = refl
localKernelEquivariant C2.flip verschiebungBranch = refl

------------------------------------------------------------------------
-- 4. Full action/orbit/stabilizer recognition.
------------------------------------------------------------------------

p3LocalToKernelActionRecognition :
  Recognition.ActionRecognitionFunctor
    p3LocalStrataAction
    Residual.constantC2Action
p3LocalToKernelActionRecognition =
  Recognition.action-recognition-functor
    localToKernel
    (λ g -> g)
    refl
    (λ g h -> refl)
    (λ g -> refl)
    localKernelEquivariant

localOrbitToResidual :
  P3LocalOrbit ->
  Residual.ConstantTernaryOrbit
localOrbitToResidual nodeOrbit = Residual.zeroConstantOrbit
localOrbitToResidual branchOrbit = Residual.nonzeroConstantOrbit

residualOrbitToLocal :
  Residual.ConstantTernaryOrbit ->
  P3LocalOrbit
residualOrbitToLocal Residual.zeroConstantOrbit = nodeOrbit
residualOrbitToLocal Residual.nonzeroConstantOrbit = branchOrbit

localOrbitRoundTrip :
  (orbit : P3LocalOrbit) ->
  residualOrbitToLocal (localOrbitToResidual orbit) ≡ orbit
localOrbitRoundTrip nodeOrbit = refl
localOrbitRoundTrip branchOrbit = refl

residualOrbitRoundTrip :
  (orbit : Residual.ConstantTernaryOrbit) ->
  localOrbitToResidual (residualOrbitToLocal orbit) ≡ orbit
residualOrbitRoundTrip Residual.zeroConstantOrbit = refl
residualOrbitRoundTrip Residual.nonzeroConstantOrbit = refl

p3LocalToKernelOrbitRecognition :
  Recognition.OrbitRecognition
    p3LocalToKernelActionRecognition
    p3LocalStrataOrbitPresentation
    Residual.constantTernaryOrbitPresentation
p3LocalToKernelOrbitRecognition =
  Recognition.orbit-recognition
    localOrbitToResidual
    orbitExact
  where
    orbitExact :
      (stratum : P3LocalStratum) ->
      Residual.constantOrbitOf (localToKernel stratum)
      ≡ localOrbitToResidual (localOrbitOf stratum)
    orbitExact frobeniusBranch = refl
    orbitExact supersingularNode = refl
    orbitExact verschiebungBranch = refl

p3LocalPi0Embedding :
  Recognition.Pi0Embedding p3LocalToKernelOrbitRecognition
p3LocalPi0Embedding =
  Recognition.pi0-embedding reflect
  where
    reflect :
      {left right : P3LocalOrbit} ->
      localOrbitToResidual left ≡ localOrbitToResidual right ->
      left ≡ right
    reflect {nodeOrbit} {nodeOrbit} same = refl
    reflect {nodeOrbit} {branchOrbit} ()
    reflect {branchOrbit} {nodeOrbit} ()
    reflect {branchOrbit} {branchOrbit} same = refl

p3LocalPi0Surjection :
  Recognition.Pi0Surjection p3LocalToKernelOrbitRecognition
p3LocalPi0Surjection =
  Recognition.pi0-surjection
    residualOrbitToLocal
    residualOrbitRoundTrip

p3LocalStabilizerRecognition :
  Recognition.StabilizerRecognition p3LocalToKernelOrbitRecognition
p3LocalStabilizerRecognition =
  Recognition.stabilizer-recognition
    representativeCompatibility
    preserves
    reflects
  where
    representativeCompatibility :
      (orbit : P3LocalOrbit) ->
      localToKernel
        (Orbit.representative p3LocalStrataOrbitPresentation orbit)
      ≡
      Orbit.representative
        Residual.constantTernaryOrbitPresentation
        (localOrbitToResidual orbit)
    representativeCompatibility nodeOrbit = refl
    representativeCompatibility branchOrbit = refl

    preserves :
      (orbit : P3LocalOrbit) ->
      (g : C2.C2) ->
      Action.act p3LocalStrataAction g
        (Orbit.representative p3LocalStrataOrbitPresentation orbit)
      ≡
      Orbit.representative p3LocalStrataOrbitPresentation orbit
      ->
      Action.act Residual.constantC2Action g
        (Orbit.representative
          Residual.constantTernaryOrbitPresentation
          (localOrbitToResidual orbit))
      ≡
      Orbit.representative
        Residual.constantTernaryOrbitPresentation
        (localOrbitToResidual orbit)
    preserves nodeOrbit C2.identity same = refl
    preserves nodeOrbit C2.flip same = refl
    preserves branchOrbit C2.identity same = refl
    preserves branchOrbit C2.flip ()

    reflects :
      (orbit : P3LocalOrbit) ->
      (g : C2.C2) ->
      Action.act Residual.constantC2Action g
        (Orbit.representative
          Residual.constantTernaryOrbitPresentation
          (localOrbitToResidual orbit))
      ≡
      Orbit.representative
        Residual.constantTernaryOrbitPresentation
        (localOrbitToResidual orbit)
      ->
      Action.act p3LocalStrataAction g
        (Orbit.representative p3LocalStrataOrbitPresentation orbit)
      ≡
      Orbit.representative p3LocalStrataOrbitPresentation orbit
    reflects nodeOrbit C2.identity same = refl
    reflects nodeOrbit C2.flip same = refl
    reflects branchOrbit C2.identity same = refl
    reflects branchOrbit C2.flip ()

p3LocalFullRecognition :
  Recognition.OrbitStabilizerRecognition
    p3LocalToKernelActionRecognition
    p3LocalStrataOrbitPresentation
    Residual.constantTernaryOrbitPresentation
p3LocalFullRecognition =
  Recognition.orbit-stabilizer-recognition
    p3LocalToKernelOrbitRecognition
    p3LocalPi0Embedding
    p3LocalPi0Surjection
    p3LocalStabilizerRecognition

------------------------------------------------------------------------
-- 5. Attribution boundary.
------------------------------------------------------------------------

classicalSourcingBoundary :
  Classical.SmallCharacteristicClassicalSourcingBoundary
classicalSourcingBoundary =
  Classical.canonicalSmallCharacteristicClassicalSourcingBoundary

data ThreeLocalStrataMeansThreeSupersingularCurves : Set where
data F9CoordinateIsClassicalLocalParameter : Set where
data LocalC2SetRecognitionIsSchemeIsomorphism : Set where

threeLocalStrataDoNotMeanThreeSupersingularCurves :
  ThreeLocalStrataMeansThreeSupersingularCurves -> ⊥
threeLocalStrataDoNotMeanThreeSupersingularCurves ()

f9CoordinateNotPromotedToClassicalLocalParameter :
  F9CoordinateIsClassicalLocalParameter -> ⊥
f9CoordinateNotPromotedToClassicalLocalParameter ()

finiteRecognitionDoesNotCreateSchemeIsomorphism :
  LocalC2SetRecognitionIsSchemeIsomorphism -> ⊥
finiteRecognitionDoesNotCreateSchemeIsomorphism ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record P3DeligneRapoportLocalStrataBoundary : Set where
  constructor p3-deligne-rapoport-local-strata-boundary
  field
    twoClassicalBranchesSourced : Bool
    uniqueSupersingularNodeSourced : Bool
    branchExchangeNodeFixingInvolutionSourced : Bool
    exactThreeStratumC2SetConstructed : Bool
    exactKernelTritRechartProved : Bool
    fullOrbitStabilizerRecognitionProved : Bool
    abstractThreeStateC2SetHasClassicalRealization : Bool
    threeDistinctSupersingularCurvesClaimed : Bool
    f9CoordinateIdentifiedAsClassicalLocalParameter : Bool
    schemeIsomorphismClaimed : Bool

canonicalP3DeligneRapoportLocalStrataBoundary :
  P3DeligneRapoportLocalStrataBoundary
canonicalP3DeligneRapoportLocalStrataBoundary =
  p3-deligne-rapoport-local-strata-boundary
    true true true true true true true false false false
