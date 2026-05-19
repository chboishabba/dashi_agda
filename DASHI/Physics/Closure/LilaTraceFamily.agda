module DASHI.Physics.Closure.LilaTraceFamily where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.ExecutionContract as EC
import DASHI.Physics.Closure.ExecutionContractLaws as ECL

-- A row in the LILA trace view: one adjacent pair plus the receipt that
-- certifies the pair against the execution contract.
record TraceRow
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    step : Nat
    current : EC.State C
    next : EC.State C
    receipt : ECL.ExecutionContractReceipt C current next

  admissible : EC.AdmissibleStep C current next
  admissible = ECL.receipt→admissible receipt

open TraceRow public

-- A trace family is the lifting layer that lets CSV-ish rows be interpreted as
-- certified execution rows.
record TraceFamily
  {ℓx ℓs ℓδ ℓπ ℓe ℓr : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔ ℓr)) where
  field
    Row : Set ℓr
    interpret : Row → TraceRow C

row→admissible :
  {ℓx ℓs ℓδ ℓπ ℓe ℓr : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  (TF : TraceFamily {ℓr = ℓr} C) →
  (row : TraceFamily.Row TF) →
  EC.AdmissibleStep C
    (TraceRow.current (TraceFamily.interpret TF row))
    (TraceRow.next (TraceFamily.interpret TF row))
row→admissible TF row =
  TraceRow.admissible (TraceFamily.interpret TF row)
