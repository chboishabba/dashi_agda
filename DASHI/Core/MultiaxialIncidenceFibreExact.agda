module DASHI.Core.MultiaxialIncidenceFibreExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.MultiaxialResidualBundleExact as Multi

------------------------------------------------------------------------
-- MULTIAXIAL INCIDENCE FIBRE
--
-- Generic owner for distinguishing technical/physical outcome from who bears
-- benefit, loss, responsibility and political contestability.  Applications
-- instantiate the coordinate meanings; this owner only preserves separation.
------------------------------------------------------------------------

record MultiaxialIncidenceFibre : Set₁ where
  field
    State : Set
    TechnicalOutcome : Set
    PhenomenonResidual : Set
    EpistemicResidual : Set
    PoliticalResidual : Set
    ResponsibilityResidual : Set
    CategoryResidual : Set

    technicalOutcomeOf : State → TechnicalOutcome
    phenomenonResidualOf : State → PhenomenonResidual
    epistemicResidualOf : State → EpistemicResidual
    politicalResidualOf : State → PoliticalResidual
    responsibilityResidualOf : State → ResponsibilityResidual
    categoryResidualOf : State → CategoryResidual

    incidenceReading : String

open MultiaxialIncidenceFibre public

residualBundleOf :
  (fibre : MultiaxialIncidenceFibre) →
  State fibre →
  Multi.ResidualBundle
    (PhenomenonResidual fibre)
    (EpistemicResidual fibre)
    (PoliticalResidual fibre)
    (ResponsibilityResidual fibre)
    (CategoryResidual fibre)
residualBundleOf fibre state =
  Multi.residualBundle
    (phenomenonResidualOf fibre state)
    (epistemicResidualOf fibre state)
    (politicalResidualOf fibre state)
    (responsibilityResidualOf fibre state)
    (categoryResidualOf fibre state)

record SameTechnicalOutcomeDifferentResponsibility
    (fibre : MultiaxialIncidenceFibre) : Set where
  field
    leftState rightState : State fibre
    sameTechnicalOutcome :
      technicalOutcomeOf fibre leftState ≡ technicalOutcomeOf fibre rightState
    responsibilityDiffers :
      responsibilityResidualOf fibre leftState
      ≡ responsibilityResidualOf fibre rightState → ⊥

open SameTechnicalOutcomeDifferentResponsibility public

responsibilityNonFactorability :
  ∀ {fibre : MultiaxialIncidenceFibre} →
  SameTechnicalOutcomeDifferentResponsibility fibre →
  NF.NonFactorabilityWitness
    (technicalOutcomeOf fibre)
    (responsibilityResidualOf fibre)
responsibilityNonFactorability witness =
  NF.nonFactorabilityWitness
    (leftState witness)
    (rightState witness)
    (sameTechnicalOutcome witness)
    (responsibilityDiffers witness)

technicalOutcomeCannotRecoverResponsibility :
  ∀ {fibre : MultiaxialIncidenceFibre} →
  SameTechnicalOutcomeDifferentResponsibility fibre →
  NF.FactorsThrough
    (technicalOutcomeOf fibre)
    (responsibilityResidualOf fibre) →
  ⊥
technicalOutcomeCannotRecoverResponsibility witness =
  NF.witnessRulesOutEveryFlatFactorisation
    (responsibilityNonFactorability witness)

record SameTechnicalOutcomeDifferentPolitics
    (fibre : MultiaxialIncidenceFibre) : Set where
  field
    politicalLeft politicalRight : State fibre
    politicalSameTechnicalOutcome :
      technicalOutcomeOf fibre politicalLeft
      ≡ technicalOutcomeOf fibre politicalRight
    politicalDiffers :
      politicalResidualOf fibre politicalLeft
      ≡ politicalResidualOf fibre politicalRight → ⊥

open SameTechnicalOutcomeDifferentPolitics public

politicalNonFactorability :
  ∀ {fibre : MultiaxialIncidenceFibre} →
  SameTechnicalOutcomeDifferentPolitics fibre →
  NF.NonFactorabilityWitness
    (technicalOutcomeOf fibre)
    (politicalResidualOf fibre)
politicalNonFactorability witness =
  NF.nonFactorabilityWitness
    (politicalLeft witness)
    (politicalRight witness)
    (politicalSameTechnicalOutcome witness)
    (politicalDiffers witness)

------------------------------------------------------------------------
-- Finite regression.
------------------------------------------------------------------------

data DemoState : Set where privatelyAbsorbed publiclyShifted : DemoState
data DemoTechnical : Set where sameRecovery : DemoTechnical
data DemoPhenomenon : Set where noPhenomenonGap : DemoPhenomenon
data DemoEpistemic : Set where noEpistemicGap : DemoEpistemic
data DemoPolitical : Set where lowContestability highContestability : DemoPolitical
data DemoResponsibility : Set where privateBurden publicBurden : DemoResponsibility
data DemoCategory : Set where sameCategory : DemoCategory

demoFibre : MultiaxialIncidenceFibre
demoFibre = record
  { State = DemoState
  ; TechnicalOutcome = DemoTechnical
  ; PhenomenonResidual = DemoPhenomenon
  ; EpistemicResidual = DemoEpistemic
  ; PoliticalResidual = DemoPolitical
  ; ResponsibilityResidual = DemoResponsibility
  ; CategoryResidual = DemoCategory
  ; technicalOutcomeOf = λ _ → sameRecovery
  ; phenomenonResidualOf = λ _ → noPhenomenonGap
  ; epistemicResidualOf = λ _ → noEpistemicGap
  ; politicalResidualOf = λ
      { privatelyAbsorbed → lowContestability
      ; publiclyShifted → highContestability
      }
  ; responsibilityResidualOf = λ
      { privatelyAbsorbed → privateBurden
      ; publiclyShifted → publicBurden
      }
  ; categoryResidualOf = λ _ → sameCategory
  ; incidenceReading = "Equal technical outcomes may coexist with different political and responsibility incidence."
  }

demoResponsibilityWitness : SameTechnicalOutcomeDifferentResponsibility demoFibre
demoResponsibilityWitness = record
  { leftState = privatelyAbsorbed
  ; rightState = publiclyShifted
  ; sameTechnicalOutcome = refl
  ; responsibilityDiffers = λ ()
  }

demoPoliticalWitness : SameTechnicalOutcomeDifferentPolitics demoFibre
demoPoliticalWitness = record
  { politicalLeft = privatelyAbsorbed
  ; politicalRight = publiclyShifted
  ; politicalSameTechnicalOutcome = refl
  ; politicalDiffers = λ ()
  }

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data TechnicalClosureImpliesPoliticalClosurePermission : Set where

data TechnicalClosureImpliesResponsibilityClosurePermission : Set where

data ResidualCarriageImpliesResidualResolutionPermission : Set where

technicalClosureDoesNotAutoPromoteToPoliticalClosure :
  TechnicalClosureImpliesPoliticalClosurePermission → ⊥
technicalClosureDoesNotAutoPromoteToPoliticalClosure ()

technicalClosureDoesNotAutoPromoteToResponsibilityClosure :
  TechnicalClosureImpliesResponsibilityClosurePermission → ⊥
technicalClosureDoesNotAutoPromoteToResponsibilityClosure ()

residualCarriageDoesNotAutoPromoteToResidualResolution :
  ResidualCarriageImpliesResidualResolutionPermission → ⊥
residualCarriageDoesNotAutoPromoteToResidualResolution ()
