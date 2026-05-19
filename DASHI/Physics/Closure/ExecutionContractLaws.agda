module DASHI.Physics.Closure.ExecutionContractLaws where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Product using (_×_; _,_)

open import DASHI.Physics.Closure.ExecutionContract as EC
open import MDL.Core.Core as OldMDL

------------------------------------------------------------------------
-- Readable receipt layer above the generic execution contract.
--
-- The base `ExecutionContract` already has the right abstract shape:
-- arrow admissibility, cone admissibility on projected deltas, MDL descent,
-- basin admissibility, and eigen-overlap admissibility.
--
-- This module does not change the contract. It packages the five obligations
-- as a named receipt surface so downstream modules can talk about execution
-- acceptance without unpacking a nested product by hand.

record ExecutionContractReceipt
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  (x x' : EC.State C)
  : Set (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe) where
  field
    arrowOK : EC.ArrowAdmissible C x x'
    coneOK : EC.ConeAdmissible C x x'
    mdlOK : EC.MDLAdmissible C x x'
    basinOK : EC.BasinAdmissible C x x'
    eigenOK : EC.EigenAdmissible C x x'

open ExecutionContractReceipt public

receipt→admissible :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C} →
  ExecutionContractReceipt C x x' →
  EC.AdmissibleStep C x x'
receipt→admissible r =
  arrowOK r
  , coneOK r
  , mdlOK r
  , basinOK r
  , eigenOK r

admissible→receipt :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C} →
  EC.AdmissibleStep C x x' →
  ExecutionContractReceipt C x x'
admissible→receipt (arrow-ok , cone-ok , mdl-ok , basin-ok , eigen-ok) =
  record
    { arrowOK = arrow-ok
    ; coneOK = cone-ok
    ; mdlOK = mdl-ok
    ; basinOK = basin-ok
    ; eigenOK = eigen-ok
    }

-- A compact theorem-facing bridge that keeps the live Lyapunov witness next
-- to the actual execution receipt instead of hiding it behind a trivial
-- compatibility lemma.
record ExecutionContractLyapunovReceipt
  {ℓx ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {lzero} {ℓδ} {ℓπ} {ℓe})
  (x x' : EC.State C)
  : Set (lsuc (ℓx ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    sourceLyapunov : OldMDL.Lyapunov (EC.sourceStep C)
    receipt : ExecutionContractReceipt C x x'

open ExecutionContractLyapunovReceipt public

bridge→admissible :
  {ℓx ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {lzero} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C} →
  ExecutionContractLyapunovReceipt C x x' →
  EC.AdmissibleStep C x x'
bridge→admissible bridge = receipt→admissible (receipt bridge)

bridge→mdl :
  {ℓx ℓδ ℓπ ℓe : Level}
  {C : EC.ExecutionContract {ℓx} {lzero} {ℓδ} {ℓπ} {ℓe}}
  {x x' : EC.State C} →
  ExecutionContractLyapunovReceipt C x x' →
  EC.MDLAdmissible C x x'
bridge→mdl {C = C} bridge = EC.admissible→mdl C (bridge→admissible bridge)

------------------------------------------------------------------------
-- Phase split: proposal channels may be rich, but truth still lives at the
-- admissibility layer. This is intentionally small and abstract.

record ExecutionContractPhaseSplit
  {ℓx ℓs ℓδ ℓπ ℓe ℓp : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe ⊔ ℓp)) where
  field
    Proposal : Set ℓp
    propose : EC.State C → Proposal
    accepted-step-implies-admissible :
      ∀ {x x'} →
      ExecutionContractReceipt C x x' →
      EC.AdmissibleStep C x x'

open ExecutionContractPhaseSplit public

canonicalPhaseSplit :
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : EC.ExecutionContract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}) →
  ExecutionContractPhaseSplit C
canonicalPhaseSplit C = record
  { Proposal = EC.State C
  ; propose = λ x → x
  ; accepted-step-implies-admissible = receipt→admissible
  }
