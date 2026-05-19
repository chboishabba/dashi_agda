module DASHI.Physics.Closure.ShiftContractMdlLevelChi2TailLiftAudit where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (_∷_; []; replicate)
open import Relation.Binary.PropositionalEquality using (sym)

open import DASHI.Algebra.Trit using (neg; pos; zer)
open import DASHI.Physics.MaskedQuadraticRenormalization as MQR using (tailOf-++)
open import DASHI.Physics.TailCollapseProof as TCP
open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as LIB
  using (caseA-state; caseB-state; caseC-state)
open import DASHI.Physics.Closure.ShiftContractMdlLevelCoarseObservable as SCMCO
  using (π-mdl-max)
open import DASHI.Physics.Closure.ShiftContractMdlLevelWitnessSearchAudit as SMWA
  using
    ( ShiftContractMdlLevelWitnessSearchAudit
    ; canonicalShiftContractMdlLevelWitnessSearchAudit
    )
open import DASHI.Physics.Closure.ShiftContractStatePrimeCompatibilityProfileInstance as SCSP
  using
    ( ShiftContractState
    ; shiftContractStateTransportedPrimeEmbedding
    )

------------------------------------------------------------------------
-- Chi2-tail lift audit on the explicit shift-contract carrier.
--
-- The raw four-trit tail patterns from the chi2 validation pool are lifted
-- directly as `ShiftContractState` values.  This gives a genuine explicit
-- same-carrier family, but the current in-tree witnesses still do not turn
-- it into a same-`π-mdl-max` / prime-image control theorem.

private
  _≢_ : {A : Set} → A → A → Set
  x ≢ y = x ≡ y → ⊥

caseA-tail : ShiftContractState
caseA-tail = neg ∷ pos ∷ neg ∷ pos ∷ []

caseB-tail : ShiftContractState
caseB-tail = pos ∷ pos ∷ neg ∷ neg ∷ []

caseC-tail : ShiftContractState
caseC-tail = neg ∷ pos ∷ pos ∷ neg ∷ []

caseA-tail-from-chi2 :
  TCP.tailOf TRI.m TRI.k caseA-state ≡ caseA-tail
caseA-tail-from-chi2 =
  tailOf-++ TRI.m TRI.k (replicate TRI.m zer) (neg ∷ pos ∷ neg ∷ pos ∷ [])

caseB-tail-from-chi2 :
  TCP.tailOf TRI.m TRI.k caseB-state ≡ caseB-tail
caseB-tail-from-chi2 =
  tailOf-++ TRI.m TRI.k (replicate TRI.m zer) (pos ∷ pos ∷ neg ∷ neg ∷ [])

caseC-tail-from-chi2 :
  TCP.tailOf TRI.m TRI.k caseC-state ≡ caseC-tail
caseC-tail-from-chi2 =
  tailOf-++ TRI.m TRI.k (replicate TRI.m zer) (neg ∷ pos ∷ pos ∷ neg ∷ [])

caseA-tail≢caseB-tail : caseA-tail ≢ caseB-tail
caseA-tail≢caseB-tail ()

caseA-tail≢caseC-tail : caseA-tail ≢ caseC-tail
caseA-tail≢caseC-tail ()

caseB-tail≢caseC-tail : caseB-tail ≢ caseC-tail
caseB-tail≢caseC-tail ()

data Chi2TailLiftOutcome : Set where
  noSameSurfaceRecovered : Chi2TailLiftOutcome

record ShiftContractMdlLevelChi2TailLiftAudit : Set₁ where
  field
    witnessSearchAudit : ShiftContractMdlLevelWitnessSearchAudit
    liftedA : ShiftContractState
    liftedB : ShiftContractState
    liftedC : ShiftContractState
    liftedA-from-chi2 :
      TCP.tailOf TRI.m TRI.k caseA-state ≡ liftedA
    liftedB-from-chi2 :
      TCP.tailOf TRI.m TRI.k caseB-state ≡ liftedB
    liftedC-from-chi2 :
      TCP.tailOf TRI.m TRI.k caseC-state ≡ liftedC
    pairwiseDistinct :
      (liftedA ≢ liftedB) × ((liftedA ≢ liftedC) × (liftedB ≢ liftedC))
    outcome : Chi2TailLiftOutcome

canonicalShiftContractMdlLevelChi2TailLiftAudit :
  ShiftContractMdlLevelChi2TailLiftAudit
canonicalShiftContractMdlLevelChi2TailLiftAudit =
  record
    { witnessSearchAudit = canonicalShiftContractMdlLevelWitnessSearchAudit
    ; liftedA = caseA-tail
    ; liftedB = caseB-tail
    ; liftedC = caseC-tail
    ; liftedA-from-chi2 = caseA-tail-from-chi2
    ; liftedB-from-chi2 = caseB-tail-from-chi2
    ; liftedC-from-chi2 = caseC-tail-from-chi2
    ; pairwiseDistinct = (caseA-tail≢caseB-tail , (caseA-tail≢caseC-tail , caseB-tail≢caseC-tail))
    ; outcome = noSameSurfaceRecovered
    }

open ShiftContractMdlLevelChi2TailLiftAudit public
