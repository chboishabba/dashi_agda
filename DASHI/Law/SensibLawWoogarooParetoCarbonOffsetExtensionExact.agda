module DASHI.Law.SensibLawWoogarooParetoCarbonOffsetExtensionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawWoogarooParetoSnowballAcquisitionExact as Pareto
import DASHI.Law.SensibLawWoogarooCarbonReplacementPopulationCrossPollinationExact as Carbon
import DASHI.Law.SensibLawWoogarooLegalConsumerAtomCompletionExact as Atom

------------------------------------------------------------------------
-- Thin extension of the existing Woogaroo Pareto router.
-- Carbon/maturity work is useful, but exact offset identity is an upstream
-- gate.  Do not let an interesting carbon calculation outrank a missing
-- same-object parcel/management-plan identity.
------------------------------------------------------------------------

data CarbonOffsetRequirement : Set where
  exactOffsetParcelIdentity
  impactReferenceCarbonAndMaturity
  offsetReferenceCarbonAndMaturity
  restorationTrajectory
  carbonStockParityTime
  habitatFunctionParityTime
  populationCapacityParityTime : CarbonOffsetRequirement

record CarbonParetoState : Set where
  constructor carbon-pareto-state
  field
    firstLiveRequirement : CarbonOffsetRequirement
    parcelIdentityPaid : Bool
    impactReferencePaid : Bool
    offsetReferencePaid : Bool
    trajectoryPaid : Bool
    carbonParityPaid : Bool
    habitatParityPaid : Bool
    populationParityPaid : Bool
    note : String

currentCarbonParetoState : CarbonParetoState
currentCarbonParetoState = carbon-pareto-state
  exactOffsetParcelIdentity
  false false false false false false false
  "Exact final offset parcel/polygon identity remains upstream. After it is paid, measure impact- and offset-side carbon/maturity states and model three separate clocks: carbon stock, habitat function and population-support capacity."

record CarbonLegalRoute : Set where
  constructor carbon-legal-route
  field
    offsetMaturityAtom : Atom.LegalExecutionAtom
    offsetLagAtom : Atom.LegalExecutionAtom
    s13EssentialityAtom : Atom.LegalExecutionAtom
    s102EffectAtom : Atom.LegalExecutionAtom
    carbonIsDirectStatutorySubstituteForHabitat : Bool
    exactIdentityBeforeQuantification : Bool

currentCarbonLegalRoute : CarbonLegalRoute
currentCarbonLegalRoute = carbon-legal-route
  Atom.offsetVegetationMaturityAtom
  Atom.offsetRestorationLagAtom
  Atom.habitatPopulationEssentialityAtom
  Atom.likelySignificantDetrimentalEffectAtom
  false true

currentMainParetoRoute : Pareto.CurrentParetoRoute
currentMainParetoRoute = Pareto.currentParetoRoute

currentCarbonAcquisition : Carbon.CarbonReplacementAcquisition
currentCarbonAcquisition = Carbon.currentCarbonReplacementAcquisition

------------------------------------------------------------------------
-- WrongType boundaries.
------------------------------------------------------------------------

data CarbonInterestingMeansCarbonFirst : Set where
data ExactOffsetIdentityCanBeSkipped : Set where
data CarbonParityPaysOffsetAdequacy : Set where
data CarbonParityPaysS13Essentiality : Set where

carbonInterestDoesNotReorderFrontier : CarbonInterestingMeansCarbonFirst → ⊥
carbonInterestDoesNotReorderFrontier ()

identityCannotBeSkipped : ExactOffsetIdentityCanBeSkipped → ⊥
identityCannotBeSkipped ()

carbonParityDoesNotPayOffsetAdequacy : CarbonParityPaysOffsetAdequacy → ⊥
carbonParityDoesNotPayOffsetAdequacy ()

carbonParityDoesNotPayS13 : CarbonParityPaysS13Essentiality → ⊥
carbonParityDoesNotPayS13 ()
