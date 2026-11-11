module DASHI.Governance.SituatedCortisolReceptorDissipativeExact where

-- DASHI original finite hormone/receptor carrier, not physical calibration.
-- Actual HPA / GR turnover, receptor regulation, FKBP5 and feedback
-- require independent biochemical and kinetic evidence. A symplectic
-- diffeomorphism preserves volume and is bijective; a dissipative update
-- that collapses distinct states cannot be such a map.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Biology.StressPhysiologyCascadeExact as HPA

data Level : Set where low middle high : Level

record HormoneReceptor : Set where
  constructor hormone-receptor
  field
    hormone : Level
    activeReceptor : Level
open HormoneReceptor public

data RegulationMode : Set where
  recovery clearance recruitment : RegulationMode

-- A demonstration of possible saturation/clearance, not a validated
-- physiological transition or a monotone stress response.
step : RegulationMode → HormoneReceptor → HormoneReceptor
step recovery s = hormone-receptor low (activeReceptor s)
step clearance s = hormone-receptor low low
step recruitment s = hormone-receptor high (activeReceptor s)

lowHormoneHighReceptor : HormoneReceptor
lowHormoneHighReceptor = hormone-receptor low high
highHormoneHighReceptor : HormoneReceptor
highHormoneHighReceptor = hormone-receptor high high
highHormoneLowReceptor : HormoneReceptor
highHormoneLowReceptor = hormone-receptor high low

sameMeasuredHormoneDifferentReceptor :
  hormone highHormoneHighReceptor ≡ hormone highHormoneLowReceptor
sameMeasuredHormoneDifferentReceptor = refl

hormoneCannotIdentifyActiveReceptor :
  NF.NonFactorabilityWitness hormone activeReceptor
hormoneCannotIdentifyActiveReceptor =
  NF.nonFactorabilityWitness
    highHormoneHighReceptor highHormoneLowReceptor refl (λ ())

clearanceCollapsesDistinctState :
  step clearance highHormoneHighReceptor
  ≡ step clearance highHormoneLowReceptor
clearanceCollapsesDistinctState = refl

differentInitialReceptorStates :
  highHormoneHighReceptor ≡ highHormoneLowReceptor → ⊥
differentInitialReceptorStates ()

-- In particular the selected clearance map has no inverse on the whole
-- state set, hence must not be introduced as an invariant symplectic flow.
clearanceHasNoGlobalLeftInverse :
  (undo : HormoneReceptor → HormoneReceptor) →
  ((s : HormoneReceptor) → undo (step clearance s) ≡ s) → ⊥
clearanceHasNoGlobalLeftInverse undo inverse =
  differentInitialReceptorStates
    (trans
      (sym (inverse highHormoneHighReceptor))
      (trans
        (cong undo clearanceCollapsesDistinctState)
        (inverse highHormoneLowReceptor)))

-- External measurement and mechanism data are required to project the
-- finite hormonal state into an actual individual concentration trace.
record ReceptorDynamicsCalibration : Set₁ where
  field
    biochemicalTimeUnit : String
    cortisolAssayUnit : String
    receptorAssaySource : String
    kineticsSourceVerified : Set
    clearanceAndProductionValidated : Set
    receptorExpressionTurnoverValidated : Set
    longitudinalSubjectFitValidated : Set
    outOfSampleFeedbackModelValidated : Set

cortisolUsesSlowerRoute :
  HPA.mediatorTimescale HPA.cortisol ≡ HPA.slowerEndocrineRoute
cortisolUsesSlowerRoute = refl
