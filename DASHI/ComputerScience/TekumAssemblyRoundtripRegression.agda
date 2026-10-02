module DASHI.ComputerScience.TekumAssemblyRoundtripRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSSPFRACTRANBridgeExact as Bridge
import DASHI.ComputerScience.TekumFieldRoleSSPAtlasExact as Atlas

regimePlusSevenRoundTrips :
  Regime.decodeRegime (Regime.regimeTrits Regime.rp7)
  ≡ Data.Maybe.just Regime.rp7
regimePlusSevenRoundTrips = refl

tekumPositiveSSPRoundTrip :
  Bridge.sspToTekumTrit (Bridge.tekumTritToSSP Trit.pos) ≡ Trit.pos
tekumPositiveSSPRoundTrip = refl

positionedNegativeReopens :
  Bridge.positionedReopen
    (Bridge.positionedProject (Bridge.positionedTrit 2 Trit.neg))
    (Bridge.positionedResidual (Bridge.positionedTrit 2 Trit.neg))
  ≡ Bridge.positionedTrit 2 Trit.neg
positionedNegativeReopens = refl

fractionLaneCanBeSeparated :
  Atlas.laneFor Atlas.separatedRoleAtlas Atlas.fractionRole ≡ Signed.ssp7
fractionLaneCanBeSeparated = refl
