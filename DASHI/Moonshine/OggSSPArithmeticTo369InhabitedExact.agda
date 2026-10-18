module DASHI.Moonshine.OggSSPArithmeticTo369InhabitedExact where

------------------------------------------------------------------------
-- INHABITED SMALL-CHARACTERISTIC ARITHMETIC -> 369 RECOGNITION
--
-- DASHI FORMAL RECONSTRUCTION
--
-- p=3 source:
--   exact F9 extension-coordinate quotient with induced Frobenius.
--
-- p=2 source:
--   distinct typed retained-orientation Gaussian-CM marked reconstruction.
--
-- This module inhabits the previously open forward recognition records and
-- their provenance first legs.  It therefore closes the entire INTERNAL
-- arithmetic-reconstruction -> residual -> independent-Base369 chain.
--
-- External identification with classical marked supersingular moduli remains
-- a separate source-authority problem and is not promoted here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Core.ActionOrbitRecognitionFunctorExact as Recognition
import DASHI.Core.ProvenancePreservingRecognitionFunctorExact as Provenance
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Action
import DASHI.Core.OrbitStabilizerResidualPresentationExact as Orbit
import DASHI.Foundations.BalancedTernaryOrbitStabilizerResidualBridgeExact as C2

import DASHI.Moonshine.OggSSPSmallCharacteristicResidualGroupoidExact as Residual
import DASHI.Moonshine.OggSSPArithmeticTo369RecognitionExact as Forward
import DASHI.Moonshine.OggSSPArithmeticToIndependent369RecognitionExact as Independent
import DASHI.Moonshine.OggSSPP3F9ExtensionQuotientSourceExact as P3Source
import DASHI.Moonshine.OggSSPP2RetainedCMMarkedSourceExact as P2Source
import DASHI.Moonshine.OggSSPP3Base369RecognitionExact as P3Bridge
import DASHI.Moonshine.OggSSPP2Base369RecognitionForkExact as P2Bridge
import DASHI.Moonshine.Base369P3ConstantTernaryActionGroupoidExact as P3Target
import DASHI.Moonshine.Base369P2FiveOrbitOrientationGroupoidsExact as P2Target
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. p=3 first leg is literally the reconstructed quotient target itself.
------------------------------------------------------------------------

p3ResidualActionRecognition :
  Recognition.ActionRecognitionFunctor
    (Residual.constantC2Action)
    Residual.constantC2Action
p3ResidualActionRecognition =
  Recognition.action-recognition-functor
    (λ state -> state)
    (λ g -> g)
    refl
    (λ g h -> refl)
    (λ g -> refl)
    (λ g state -> refl)

p3ResidualOrbitRecognition :
  Recognition.OrbitRecognition
    p3ResidualActionRecognition
    Residual.constantTernaryOrbitPresentation
    Residual.constantTernaryOrbitPresentation
p3ResidualOrbitRecognition =
  Recognition.orbit-recognition
    (λ orbit -> orbit)
    (λ state -> refl)

p3ResidualPi0Embedding :
  Recognition.Pi0Embedding p3ResidualOrbitRecognition
p3ResidualPi0Embedding =
  Recognition.pi0-embedding
    (λ same -> same)

p3ResidualPi0Surjection :
  Recognition.Pi0Surjection p3ResidualOrbitRecognition
p3ResidualPi0Surjection =
  Recognition.pi0-surjection
    (λ orbit -> orbit)
    (λ orbit -> refl)

p3ResidualStabilizerRecognition :
  Recognition.StabilizerRecognition p3ResidualOrbitRecognition
p3ResidualStabilizerRecognition =
  Recognition.stabilizer-recognition
    (λ orbit -> refl)
    (λ orbit g fixed -> fixed)
    (λ orbit g fixed -> fixed)

p3ResidualFullRecognition :
  Recognition.OrbitStabilizerRecognition
    p3ResidualActionRecognition
    Residual.constantTernaryOrbitPresentation
    Residual.constantTernaryOrbitPresentation
p3ResidualFullRecognition =
  Recognition.orbit-stabilizer-recognition
    p3ResidualOrbitRecognition
    p3ResidualPi0Embedding
    p3ResidualPi0Surjection
    p3ResidualStabilizerRecognition

canonicalP3ArithmeticTo369Recognition :
  Forward.P3ArithmeticTo369Recognition
    P3Source.canonicalP3MarkedFrobeniusSource
canonicalP3ArithmeticTo369Recognition =
  record
    { functor =
        p3ResidualActionRecognition
    ; fullRecognition =
        p3ResidualFullRecognition
    }

------------------------------------------------------------------------
-- 2. p=2 first leg is the exact source-native rechart proved by P2Source.
------------------------------------------------------------------------

canonicalP2ArithmeticTo369Recognition :
  Forward.P2ArithmeticTo369Recognition
    P2Source.canonicalP2MarkedArithmeticSource
canonicalP2ArithmeticTo369Recognition =
  record
    { functor =
        P2Source.p2CMToResidualActionRecognition
    ; fullRecognition =
        P2Source.p2CMToResidualFullRecognition
    }

------------------------------------------------------------------------
-- 3. Direct independent-Base369 recognitions now inhabit by composition.
------------------------------------------------------------------------

canonicalP3ArithmeticToIndependent369 :
  Recognition.OrbitStabilizerRecognition
    (Independent.p3IndependentFunctor
      canonicalP3ArithmeticTo369Recognition)
    (Residual.constantTernaryOrbitPresentation)
    P3Target.p3OrbitPresentation
canonicalP3ArithmeticToIndependent369 =
  Independent.p3IndependentFullRecognition
    canonicalP3ArithmeticTo369Recognition

canonicalP2ArithmeticToIndependent369 :
  Recognition.OrbitStabilizerRecognition
    (Independent.p2IndependentFunctor
      canonicalP2ArithmeticTo369Recognition)
    P2Source.p2CMOrbitPresentation
    P2Target.p2RetainedOrbitPresentation
canonicalP2ArithmeticToIndependent369 =
  Independent.p2IndependentFullRecognition
    canonicalP2ArithmeticTo369Recognition

------------------------------------------------------------------------
-- 4. p=3 provenance first leg.
------------------------------------------------------------------------

p3ArithmeticProvenance :
  Residual.ConstantTernaryState ->
  P3Bridge.SourceProvenance
p3ArithmeticProvenance state = state

p3ProvenanceActionRecognition :
  Provenance.ProvenancePreservingActionRecognition
    Residual.constantC2Action
    Residual.constantC2Action
    p3ArithmeticProvenance
    P3Bridge.sourceProvenance
p3ProvenanceActionRecognition =
  Provenance.provenance-preserving-action-recognition
    p3ResidualActionRecognition
    (λ provenance -> provenance)
    (λ state -> refl)
    (λ same -> same)

p3ProvenanceOrbitRecognition :
  Provenance.ProvenancePreservingOrbitRecognition
    p3ProvenanceActionRecognition
    Residual.constantTernaryOrbitPresentation
    Residual.constantTernaryOrbitPresentation
p3ProvenanceOrbitRecognition =
  Provenance.provenance-preserving-orbit-recognition
    p3ResidualOrbitRecognition
    p3ResidualPi0Embedding
    p3ResidualPi0Surjection
    p3ResidualStabilizerRecognition

canonicalP3ArithmeticProvenanceFirstLeg :
  Independent.P3ArithmeticProvenanceFirstLeg
    P3Source.canonicalP3MarkedFrobeniusSource
canonicalP3ArithmeticProvenanceFirstLeg =
  record
    { ArithmeticProvenance =
        P3Bridge.SourceProvenance
    ; arithmeticProvenance =
        p3ArithmeticProvenance
    ; firstLegAction =
        p3ProvenanceActionRecognition
    ; firstLegOrbit =
        p3ProvenanceOrbitRecognition
    }

canonicalP3IndependentProvenanceRecognition =
  Independent.p3IndependentProvenanceRecognition
    canonicalP3ArithmeticProvenanceFirstLeg

------------------------------------------------------------------------
-- 5. p=2 orientation provenance first leg.
------------------------------------------------------------------------

p2ArithmeticProvenance :
  P2Source.P2CMMarkedState ->
  P2Source.CMOrientation
p2ArithmeticProvenance =
  P2Source.orientation

p2ProvenanceActionRecognition :
  Provenance.ProvenancePreservingActionRecognition
    P2Source.p2CMAction
    Residual.p2DiscreteAction
    p2ArithmeticProvenance
    P2Bridge.sourceOrientationProvenance
p2ProvenanceActionRecognition =
  Provenance.provenance-preserving-action-recognition
    P2Source.p2CMToResidualActionRecognition
    P2Source.cmOrientationToSide
    (λ state -> refl)
    reflect
  where
    reflect :
      {left right : P2Source.P2CMMarkedState} ->
      P2Bridge.sourceOrientationProvenance (P2Source.toResidual left)
      ≡
      P2Bridge.sourceOrientationProvenance (P2Source.toResidual right)
      ->
      p2ArithmeticProvenance left ≡ p2ArithmeticProvenance right
    reflect {P2Source.cm-marked-state P2Source.cmLower leftOrbit}
            {P2Source.cm-marked-state P2Source.cmLower rightOrbit}
            same = refl
    reflect {P2Source.cm-marked-state P2Source.cmLower leftOrbit}
            {P2Source.cm-marked-state P2Source.cmUpper rightOrbit}
            ()
    reflect {P2Source.cm-marked-state P2Source.cmUpper leftOrbit}
            {P2Source.cm-marked-state P2Source.cmLower rightOrbit}
            ()
    reflect {P2Source.cm-marked-state P2Source.cmUpper leftOrbit}
            {P2Source.cm-marked-state P2Source.cmUpper rightOrbit}
            same = refl

p2ProvenanceOrbitRecognition :
  Provenance.ProvenancePreservingOrbitRecognition
    p2ProvenanceActionRecognition
    P2Source.p2CMOrbitPresentation
    Residual.p2DiscreteOrbitPresentation
p2ProvenanceOrbitRecognition =
  Provenance.provenance-preserving-orbit-recognition
    P2Source.p2CMToResidualOrbitRecognition
    P2Source.p2CMToResidualPi0Embedding
    P2Source.p2CMToResidualPi0Surjection
    P2Source.p2CMToResidualStabilizerRecognition

canonicalP2ArithmeticProvenanceFirstLeg :
  Independent.P2ArithmeticProvenanceFirstLeg
    P2Source.canonicalP2MarkedArithmeticSource
canonicalP2ArithmeticProvenanceFirstLeg =
  record
    { ArithmeticProvenance =
        P2Source.CMOrientation
    ; arithmeticProvenance =
        p2ArithmeticProvenance
    ; firstLegAction =
        p2ProvenanceActionRecognition
    ; firstLegOrbit =
        p2ProvenanceOrbitRecognition
    }

canonicalP2IndependentProvenanceRecognition =
  Independent.p2IndependentProvenanceRecognition
    canonicalP2ArithmeticProvenanceFirstLeg

------------------------------------------------------------------------
-- 6. Internal closure / external authority boundary.
------------------------------------------------------------------------

data InternalArithmeticRecognitionStillUninhabited : Set where
data InternalArithmeticProvenanceStillUninhabited : Set where
data InternalClosureCreatesExternalClassicalModuliIdentification : Set where

internalArithmeticRecognitionIsInhabited :
  InternalArithmeticRecognitionStillUninhabited -> ⊥
internalArithmeticRecognitionIsInhabited ()

internalArithmeticProvenanceIsInhabited :
  InternalArithmeticProvenanceStillUninhabited -> ⊥
internalArithmeticProvenanceIsInhabited ()

internalClosureDoesNotCreateExternalClassicalModuliIdentification :
  InternalClosureCreatesExternalClassicalModuliIdentification -> ⊥
internalClosureDoesNotCreateExternalClassicalModuliIdentification ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin =
  Attribution.repositoryFormalReconstruction

record ArithmeticTo369InhabitedBoundary : Set where
  constructor arithmetic-to369-inhabited-boundary
  field
    p3SourceSocketInhabited : Bool
    p2SourceSocketInhabited : Bool
    p3ForwardRecognitionInhabited : Bool
    p2ForwardRecognitionInhabited : Bool
    p3IndependentRecognitionInhabited : Bool
    p2IndependentRecognitionInhabited : Bool
    p3ProvenanceFirstLegInhabited : Bool
    p2ProvenanceFirstLegInhabited : Bool
    p3IndependentProvenanceRecognitionInhabited : Bool
    p2IndependentProvenanceRecognitionInhabited : Bool
    repositoryFormalReconstruction : Bool
    externalClassicalModuliIdentificationPaid : Bool

canonicalArithmeticTo369InhabitedBoundary :
  ArithmeticTo369InhabitedBoundary
canonicalArithmeticTo369InhabitedBoundary =
  arithmetic-to369-inhabited-boundary
    true true true true true true true true true true true false
