module DASHI.Culture.AmyEskridgeHistoricalMechanismBidiSourceWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Culture.AmyEskridgeHAL5PrimaryLiteratureSnowballExact as Sources
import DASHI.Physics.ExoticGravity.EngineeredInertialGravitationalBidiExact as Bidi

------------------------------------------------------------------------
-- AMY HISTORICAL SOURCE -> EXISTING BIDI FAMILY WELD
--
-- This is a bounded source-routing adapter.  The historical source atom chooses
-- which already-existing mechanism family / observable deserves reverse-search
-- attention.  It does not turn the published claim into an observation receipt,
-- replicate the experiment, or attribute DASHI's modern interpretation to Amy.
------------------------------------------------------------------------

record HistoricalMechanismBidiWeld : Set where
  constructor historical-mechanism-bidi-weld
  field
    sourceAtom : Sources.AmyPrimaryLiteratureSnowballAtom
    mechanismFamily : Bidi.MechanismFamily
    primaryObservable : Bidi.Observable
    reverseSearchTarget : String
    exactEquationCarrierStillRequired : Bool
    sameApparatusExperimentalReceiptStillRequired : Bool
    ordinaryConfounderClosureStillRequired : Bool
    independentReplicationStillRequired : Bool

open HistoricalMechanismBidiWeld public

liTorrHistoricalBidiWeld : HistoricalMechanismBidiWeld
liTorrHistoricalBidiWeld =
  historical-mechanism-bidi-weld
    Sources.liTorr1991Atom
    Bidi.liTorrCoherentGravity
    Bidi.localTestMassAcceleration
    "source-entitled Li-Torr equations -> component-resolved mass current -> laboratory stress-energy -> same-apparatus external gravity-channel observable"
    true true true true

podkletnovHistoricalBidiWeld : HistoricalMechanismBidiWeld
podkletnovHistoricalBidiWeld =
  historical-mechanism-bidi-weld
    Sources.podkletnov1992Atom
    Bidi.podkletnovWeightAnomaly
    Bidi.staticWeightChange
    "reconstruct the reported 1992 configuration and measured apparent-weight channel, then compare against exact-apparatus EM/mechanical/thermal/vibration controls and published replication constraints"
    true true true true

woodwardHistoricalBidiWeld : HistoricalMechanismBidiWeld
woodwardHistoricalBidiWeld =
  historical-mechanism-bidi-weld
    Sources.woodward1992Atom
    Bidi.woodwardInertialVariation
    Bidi.inertialResponseChange
    "inspect exact transient-mass equation and synchronous-thrust phase relation, then require momentum accounting and an inertial comparison on the same apparatus"
    true true true true

record HistoricalMechanismBidiBoundary : Set where
  constructor historical-mechanism-bidi-boundary
  field
    abstractClaimCreatesObservationReceipt : Bool
    historicalReportedEffectCreatesReplication : Bool
    amyDeckMentionCreatesModernMechanismProof : Bool
    sourceAtomMayChooseReverseSearchFamily : Bool
    exactPrimaryCarrierStillControlsEquationAttribution : Bool
    experimentalClaimStillRequiresSameApparatusValidation : Bool

canonicalHistoricalMechanismBidiBoundary : HistoricalMechanismBidiBoundary
canonicalHistoricalMechanismBidiBoundary =
  historical-mechanism-bidi-boundary false false false true true true
