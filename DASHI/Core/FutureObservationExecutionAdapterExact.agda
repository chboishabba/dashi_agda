module DASHI.Core.FutureObservationExecutionAdapterExact where

-- Same-action forward and reverse execution transport into the EXISTING
-- future-language summary. No second equivalence or quotient ontology.
-- The two local edge-lift obligations are explicit: common-trace
-- congruence alone cannot ensure preservation of enabledness.
-- Source-written, kernel acceptance pending.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; subst; cong; trans)
import DASHI.Core.TypedDependencyCore as D
import DASHI.Core.AdmissibleReachability as R
import DASHI.Core.FutureObservationLanguageQuotientExact as F

module ExecutionAdapter
  {State Coarse Action Observation : Set}
  (fine : D.DependentActionSystem State Action)
  (coarse : D.DependentActionSystem Coarse Action)
  (q : State → Coarse)
  (observe : Coarse → Observation)
  (forwardEdge :
    ∀ {s a} (e : D.AdmissibleAction fine s a) →
    Σ (D.AdmissibleAction coarse (q s) a)
      (λ e′ → D.after e′ ≡ q (D.after e)))
  (backwardEdge :
    ∀ {s a} (e′ : D.AdmissibleAction coarse (q s) a) →
    Σ (D.AdmissibleAction fine s a)
      (λ e → q (D.after e) ≡ D.after e′))
  where

  projectExecution :
    ∀ {word s t} →
    R.Executes fine word s t →
    R.Executes coarse word (q s) (q t)
  projectExecution R.executesNil = R.executesNil
  projectExecution (R.executesCons {target = t} {actions = restWord} e rest)
    with forwardEdge e
  ... | e′ , edgeEq =
    R.executesCons e′
      (subst (λ start → R.Executes coarse restWord start (q t))
        (sym edgeEq) (projectExecution rest))

  -- Carry the starting-code equality as an explicit index. The recursive
  -- argument remains the actual structural subtrace, not a transported
  -- or fabricated new execution.
  liftExecution :
    ∀ {word s c target} →
    q s ≡ c →
    R.Executes coarse word c target →
    Σ State (λ t → R.Executes fine word s t × (q t ≡ target))
  liftExecution {s = s} refl R.executesNil =
    s , (R.executesNil , refl)
  liftExecution {s = s} refl (R.executesCons e′ rest)
    with backwardEdge {s = s} e′
  ... | e , edgeEq with liftExecution {s = D.after e} edgeEq rest
  ... | t , (run , endEq) =
    t , (R.executesCons e run , endEq)

  sourceObservation : State → Observation
  sourceObservation s = observe (q s)

  forwardFuture :
    ∀ {s word o} →
    F.FutureObservation fine sourceObservation s word o →
    F.FutureObservation coarse observe (q s) word o
  forwardFuture (F.futureObservation t run seen) =
    F.futureObservation (q t) (projectExecution run) seen

  backwardFuture :
    ∀ {s word o} →
    F.FutureObservation coarse observe (q s) word o →
    F.FutureObservation fine sourceObservation s word o
  backwardFuture {s = s} (F.futureObservation target run seen)
    with liftExecution {s = s} refl run
  ... | t , (fineRun , endEq) =
    F.futureObservation t fineRun (trans (cong observe endEq) seen)

  exactSummary : F.ExactFutureLanguageSummary fine sourceObservation q
  exactSummary = record
    { SummaryLanguage = λ c word o →
        F.FutureObservation coarse observe c word o
    ; summaryExact = λ s word o →
        F.logicalIff forwardFuture backwardFuture
    }

  originalFutureLanguageSafe :
    F.FutureLanguageSafeProjection fine sourceObservation q
  originalFutureLanguageSafe =
    F.exactSummaryCertifiesFutureLanguageSafety exactSummary

-- This adapter charges no resource itself. Cost/event observations must
-- be carried in the state/observation or certified separately on each
-- lifted edge; semantic equivalence alone implies no time bound.
