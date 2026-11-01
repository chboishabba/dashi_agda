module DASHI.Physics.Closure.LilaDashiBridge where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.Unit.Polymorphic using (⊤)

open import DASHI.Physics.Closure.ExecutionContract as EC
open import DASHI.Physics.Closure.ExecutionContractLaws as ECL
open import DASHI.Physics.Closure.BadModeSuppression as BMS

-- LILA is treated here as the execution-side system.
-- DASHI is the admissibility lens that reads and packages the execution trace.
record LilaDashiBridge
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    execution : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}
    phaseSplit : ECL.ExecutionContractPhaseSplit {ℓp = ℓx} execution
    badMode : BMS.BadModeSuppressionContract (EC.State execution)

open LilaDashiBridge public

canonicalLilaDashiBridge :
  {ℓx ℓs ℓδ ℓπ ℓe : Level} →
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}) →
  LilaDashiBridge {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}
canonicalLilaDashiBridge C = record
  { execution = C
  ; phaseSplit = ECL.canonicalPhaseSplit C
  ; badMode = record
      { surface = record
          { step = λ s → s
          ; badMass = λ _ → 0
          ; coherenceReached = λ _ → ⊤
          }
      ; eventualSafeBias = ⊤
      }
  }
