module DASHI.Analysis.RiemannUniversalEvenConeTransportGateExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Analysis.RiemannAristotleUniversalEvenConeBidiExact as Universal
import DASHI.Analysis.RiemannG2PhaseWeldCellwiseUpperBridgeExact as Upper

------------------------------------------------------------------------
-- UNIVERSAL EVEN-CONE SAME-OBJECT TRANSPORT GATE
--
-- The source-side Lean lane already owns a nonnegative universal pole-quotient
-- taper with exact pole annihilation and positive same-ordinate response.  The
-- remaining first payment is not another taper design: it is transporting that
-- exact object onto the final Agda pole-quotient carrier consumed downstream.
--
-- Once the same-object transport is available, nonnegativity is exactly the
-- property needed to feed a positive-part phase majorant into the existing
-- one-sided cell/fold upper route.  This gate does not pay Gamma or the signed
-- off-ordinate estimate by itself.
------------------------------------------------------------------------

universalReturn : Universal.UniversalEvenConeReturn
universalReturn = Universal.canonicalUniversalEvenConeReturn

upperBoundary : Upper.PhaseWeldCellwiseUpperBridgeBoundary
upperBoundary = Upper.canonicalPhaseWeldCellwiseUpperBridgeBoundary

record UniversalEvenConeTransportCandidate : Set₁ where
  constructor universal-even-cone-transport-candidate
  field
    SourceTaper : Set
    FinalPoleQuotientTaper : Set
    sourceTaper : SourceTaper
    finalTaper : FinalPoleQuotientTaper

    sameObjectTransport : Set
    transportedTaperIsSourceTaper : Set

    sourceTaperNonnegative : Set
    sourcePoleClassKilledExactly : Set
    sourceSameOrdinateClusterPositive : Set

    finalTaperNonnegative : Set
    finalPoleClassKilledExactly : Set
    finalSameOrdinateClusterPositive : Set

    positivePartPhaseMajorantAvailable : Set
open UniversalEvenConeTransportCandidate public

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data SourceExistenceCreatesAgdaTransport : Set where
data OEISNumericalPatternCreatesTaperTransport : Set where
data PositivePartMajorantClosesGamma : Set where
data PositivePartMajorantClosesSignedOffOrdinateTail : Set where

sourceExistenceDoesNotCreateTransport : SourceExistenceCreatesAgdaTransport -> ⊥
sourceExistenceDoesNotCreateTransport ()

oeisDoesNotCreateTaperTransport : OEISNumericalPatternCreatesTaperTransport -> ⊥
oeisDoesNotCreateTaperTransport ()

positivePartMajorantDoesNotCloseGamma : PositivePartMajorantClosesGamma -> ⊥
positivePartMajorantDoesNotCloseGamma ()

positivePartMajorantDoesNotCloseSignedTail :
  PositivePartMajorantClosesSignedOffOrdinateTail -> ⊥
positivePartMajorantDoesNotCloseSignedTail ()

record UniversalEvenConeTransportBoundary : Set where
  constructor universal-even-cone-transport-boundary
  field
    sourceUniversalTaperOwned : Bool
    sameObjectTransportInterfaceSpecified : Bool
    nonnegativeTaperFeedsPositivePartMajorant : Bool
    existingOneSidedCellUpperRouteReusable : Bool

    sameObjectTransportPaid : Bool
    positivePartMajorantAuthorityPaid : Bool
    signedOffOrdinateTailPaid : Bool
    gammaPaid : Bool

    sourceExistenceCreatesAgdaTransport : Bool
    oeisNumericalPatternCreatesTaperTransport : Bool
    positivePartMajorantClosesGamma : Bool
open UniversalEvenConeTransportBoundary public

canonicalUniversalEvenConeTransportBoundary : UniversalEvenConeTransportBoundary
canonicalUniversalEvenConeTransportBoundary =
  universal-even-cone-transport-boundary
    true true true true
    false false false false
    false false false
