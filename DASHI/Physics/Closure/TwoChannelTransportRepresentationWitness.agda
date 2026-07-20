module DASHI.Physics.Closure.TwoChannelTransportRepresentationWitness where

-- First concrete physical/dynamical witness for representation compatibility.
--
-- Fine state keeps two directed transport channels.  One kernel step exchanges
-- their roles.  Coarse state retains total transported content only, so its
-- kernel is the identity.  Projection commutes exactly with evolution because
-- total content is invariant under channel exchange.
--
-- This is intentionally a minimal transport carrier, not a general wave,
-- continuum, or spacetime theorem.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _≤_)
open import Data.Nat.Properties using (+-comm; ≤-refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)

import DASHI.Physics.PhysicalTheory as PT
import DASHI.Physics.Closure.RepresentationKernelCompatibility as RKC

FineTransportState : Set
FineTransportState = Nat × Nat

CoarseTransportState : Set
CoarseTransportState = Nat

fineTransportStep : FineTransportState → FineTransportState
fineTransportStep x = proj₂ x , proj₁ x

coarseTransportStep : CoarseTransportState → CoarseTransportState
coarseTransportStep total = total

projectTransport : FineTransportState → CoarseTransportState
projectTransport x = proj₁ x + proj₂ x

fineTransportObservable : FineTransportState → Nat
fineTransportObservable = projectTransport

coarseTransportObservable : CoarseTransportState → Nat
coarseTransportObservable total = total

fineTransportAdmissible : FineTransportState → Set
fineTransportAdmissible _ = ⊤

coarseTransportAdmissible : CoarseTransportState → Set
coarseTransportAdmissible _ = ⊤

transportProjectionCommutes :
  ∀ {x} →
  fineTransportAdmissible x →
  projectTransport (fineTransportStep x)
  ≡
  coarseTransportStep (projectTransport x)
transportProjectionCommutes {x} _ =
  +-comm (proj₂ x) (proj₁ x)

transportObservablePreserved :
  ∀ x →
  coarseTransportObservable (projectTransport x)
  ≡
  fineTransportObservable x
transportObservablePreserved _ = refl

canonicalTransportRepresentationLaw :
  RKC.RepresentationKernelCompatibility
canonicalTransportRepresentationLaw =
  record
    { FineState = FineTransportState
    ; CoarseState = CoarseTransportState
    ; Observable = Nat
    ; fineStep = fineTransportStep
    ; coarseStep = coarseTransportStep
    ; project = projectTransport
    ; fineAdmissible = fineTransportAdmissible
    ; coarseAdmissible = coarseTransportAdmissible
    ; fineObserve = fineTransportObservable
    ; coarseObserve = coarseTransportObservable
    ; fineAdmissibleStep = λ _ → tt
    ; coarseAdmissibleStep = λ _ → tt
    ; projectPreservesAdmissibility = λ _ → tt
    ; projectPreservesObservable = transportObservablePreserved
    ; kernelCommutesWithProjection = transportProjectionCommutes
    }

transportTrajectoryCommutes :
  ∀ x n →
  projectTransport (RKC.iterate fineTransportStep n x)
  ≡
  RKC.iterate coarseTransportStep n (projectTransport x)
transportTrajectoryCommutes x n =
  RKC.trajectoryCommutes canonicalTransportRepresentationLaw tt n

------------------------------------------------------------------------
-- The same carrier packaged through the existing PhysicalTheory interface.

fineTransportTheory : PT.PhysicalTheory _
fineTransportTheory =
  record
    { State = FineTransportState
    ; step = fineTransportStep
    ; Defect = λ _ → ⊤
    ; defectSize = λ _ → 0
    ; Inv = fineTransportAdmissible
    ; inv-step = λ _ → tt
    ; defect-monotone = λ _ → ≤-refl
    ; fixed = RKC.FixedPoint fineTransportStep
    ; recoveredLaw = λ x → projectTransport (fineTransportStep x) ≡ projectTransport x
    }

coarseTransportTheory : PT.PhysicalTheory _
coarseTransportTheory =
  record
    { State = CoarseTransportState
    ; step = coarseTransportStep
    ; Defect = λ _ → ⊤
    ; defectSize = λ _ → 0
    ; Inv = coarseTransportAdmissible
    ; inv-step = λ _ → tt
    ; defect-monotone = λ _ → ≤-refl
    ; fixed = RKC.FixedPoint coarseTransportStep
    ; recoveredLaw = λ x → coarseTransportStep x ≡ x
    }
