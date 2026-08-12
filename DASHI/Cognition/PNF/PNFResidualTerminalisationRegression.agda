module DASHI.Cognition.PNF.PNFResidualTerminalisationRegression where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Cognition.PNF.EventAlgebra as PNF

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

hasUnresolvedResidual : PNF.ResolvedPNF → Bool
hasUnresolvedResidual resolved with PNF.unresolvedResidual resolved
... | [] = false
... | _ ∷ _ = true

record ResolvedPNFShadowState : Set where
  constructor resolvedPNFShadowState
  field
    resolvedPNF : PNF.ResolvedPNF
    residualOutcome : Bool

open ResolvedPNFShadowState public

data ResidualInspection : Set where inspectResidual : ResidualInspection

inspectResidualStep : ResolvedPNFShadowState → ResolvedPNFShadowState
inspectResidualStep state =
  resolvedPNFShadowState
    (resolvedPNF state)
    (hasUnresolvedResidual (resolvedPNF state))

resolvedPNFInspectionSystem :
  Dependency.DependentActionSystem
    ResolvedPNFShadowState ResidualInspection
resolvedPNFInspectionSystem = record
  { Precondition = λ state action → ⊤
  ; Postcondition = λ before action after → after ≡ inspectResidualStep before
  ; actionLabel = λ action → "inspect retained PNF residual"
  }

inspectionAdmissible :
  (state : ResolvedPNFShadowState) →
  Dependency.AdmissibleAction
    resolvedPNFInspectionSystem state inspectResidual
inspectionAdmissible state = record
  { precondition = tt
  ; after = inspectResidualStep state
  ; postcondition = refl
  ; dependencyReceipt = "consumer inspects unresolved PNF residual"
  }

inspectionExecution :
  (state : ResolvedPNFShadowState) →
  Reachability.Executes
    resolvedPNFInspectionSystem
    (inspectResidual ∷ [])
    state
    (inspectResidualStep state)
inspectionExecution state =
  Reachability.executesCons
    (inspectionAdmissible state)
    Reachability.executesNil

PNFPublicShadow : Set
PNFPublicShadow = PNF.EventPNF × Bool

resolvedPNFPublicProjection : ResolvedPNFShadowState → PNFPublicShadow
resolvedPNFPublicProjection state =
  PNF.sourcePNF (resolvedPNF state) , residualOutcome state

resolvedPNFResidualTerminalisationDefect :
  (left right : PNF.ResolvedPNF) →
  PNF.sourcePNF left ≡ PNF.sourcePNF right →
  hasUnresolvedResidual left ≡ true →
  hasUnresolvedResidual right ≡ false →
  Dynamic.TerminalisationDefect
    resolvedPNFInspectionSystem
    resolvedPNFPublicProjection
resolvedPNFResidualTerminalisationDefect
    left right sameSource leftHasResidual rightHasNoResidual =
  Dynamic.terminalisationDefect
    (inspectResidual ∷ [])
    (resolvedPNFShadowState left false)
    (resolvedPNFShadowState right false)
    (inspectResidualStep (resolvedPNFShadowState left false))
    (inspectResidualStep (resolvedPNFShadowState right false))
    (cong (λ source → source , false) sameSource)
    (inspectionExecution (resolvedPNFShadowState left false))
    (inspectionExecution (resolvedPNFShadowState right false))
    futureDiff
  where
  futureDiff :
    resolvedPNFPublicProjection
      (inspectResidualStep (resolvedPNFShadowState left false))
    ≡
    resolvedPNFPublicProjection
      (inspectResidualStep (resolvedPNFShadowState right false)) → ⊥
  futureDiff equality =
    trueNotFalse
      (trans
        (sym leftHasResidual)
        (trans (cong proj₂ equality) rightHasNoResidual))
