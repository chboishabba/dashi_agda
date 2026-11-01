module DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat.Properties as NatP using (≤-refl)
open import Data.Product using (_×_; _,_)
open import Data.Vec using (_∷_; _++_; replicate; [])

open import UFTC_Lattice using (special; severity)
open import DASHI.Algebra.Trit using (neg; pos; zer)
open import DASHI.Physics.RealTernaryCarrier as RTC
open import DASHI.Physics.TernaryRealInstance as TRI
open import DASHI.Physics.SeverityMapping as SM
open import DASHI.Physics.SeverityGuard.Core as SG
open import DASHI.Physics.SeverityGuard.Shift.Concrete as SGSC

record Chi2BoundaryCase : Set where
  field
    label : String
    state : RTC.Carrier TRI.n
    code-special4 : SM.codeᵣ {TRI.m} {TRI.k} state ≡ special 4
    severity4 :
      severity (SG.SeverityPolicy.code (SGSC.policyᵣ {TRI.m} {TRI.k}) state) ≡ 4
    snapWitness : SG.Snap (SGSC.policyᵣ {TRI.m} {TRI.k}) state
    brokenWitness : SG.Broken (SGSC.policyᵣ {TRI.m} {TRI.k}) state

caseA-state : RTC.Carrier TRI.n
caseA-state =
  replicate TRI.m zer ++ (neg ∷ pos ∷ neg ∷ pos ∷ [])

caseA : Chi2BoundaryCase
caseA =
  record
    { label = "tail-alt-signs"
    ; state = caseA-state
    ; code-special4 = refl
    ; severity4 = refl
    ; snapWitness = NatP.≤-refl
    ; brokenWitness = NatP.≤-refl
    }

caseB-state : RTC.Carrier TRI.n
caseB-state =
  replicate TRI.m zer ++ (pos ∷ pos ∷ neg ∷ neg ∷ [])

caseB : Chi2BoundaryCase
caseB =
  record
    { label = "tail-block-signs"
    ; state = caseB-state
    ; code-special4 = refl
    ; severity4 = refl
    ; snapWitness = NatP.≤-refl
    ; brokenWitness = NatP.≤-refl
    }

caseC-state : RTC.Carrier TRI.n
caseC-state =
  replicate TRI.m zer ++ (neg ∷ pos ∷ pos ∷ neg ∷ [])

caseC : Chi2BoundaryCase
caseC =
  record
    { label = "tail-cross-signs"
    ; state = caseC-state
    ; code-special4 = refl
    ; severity4 = refl
    ; snapWitness = NatP.≤-refl
    ; brokenWitness = NatP.≤-refl
    }

caseCount : Nat
caseCount = 3

primarySecondary : Chi2BoundaryCase × Chi2BoundaryCase
primarySecondary = caseA , caseB
