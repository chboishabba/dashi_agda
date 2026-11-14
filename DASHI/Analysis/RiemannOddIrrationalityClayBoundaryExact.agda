module DASHI.Analysis.RiemannOddIrrationalityClayBoundaryExact where

------------------------------------------------------------------------
-- ATTRIBUTION / ADMISSION
--
-- External mathematics: W. Zudilin (arXiv:1801.09895), odd zeta irrationality.
-- External Lean formalization: no revision/axiom audit admitted here.
-- DASHI: exact evidence separation and countermodel for a GENERIC claim.
--
-- This does not give a model of the real Riemann zeta function with an off-line
-- zero. It shows that abstract odd-value irrationality transport alone does
-- not entail exclusion of independent off-line states.
--
-- RH owner: RiemannMillenniumAssembly, actual analytic/Weil hypotheses open.
-- Hermitian owner: RiemannHermitianEndgameTrichotomyExact, G1-G4 open.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (_,_)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Fin using (zero)

import DASHI.Analysis.ZetaOddValueWitnessTransportExact as Odd
import DASHI.Analysis.RiemannAnalyticSubstrate as Analytic
import DASHI.Analysis.RiemannMillenniumAssembly as Weil
import DASHI.Analysis.RiemannHermitianEndgameTrichotomyExact as Hermitian

------------------------------------------------------------------------
-- An ordinary conjunction of evidence is not a proof transfer from one
-- independent domain to another. Each result uses its own actual producer.
------------------------------------------------------------------------

record JointWeilOddEvidence : Set₁ where
  field
    oddContext : Odd.ValueContext
    oddWitness :
      Odd.OddIrrationalWitness oddContext
        (Odd.ValueContext.leanValue oddContext)
    rhAssembly : Weil.DashiRiemannAssembly

open JointWeilOddEvidence

jointEvidenceYieldsOddDashi :
  (evidence : JointWeilOddEvidence) →
  Odd.OddIrrationalWitness (oddContext evidence)
    (Odd.ValueContext.dashiValue (oddContext evidence))
jointEvidenceYieldsOddDashi evidence =
  Odd.leanToDashiIrrationalWitnessDirect
    (oddContext evidence) (oddWitness evidence)

jointEvidenceYieldsRH :
  (evidence : JointWeilOddEvidence) →
  Analytic.RiemannHypothesisFor
    (Weil.DashiRiemannAssembly.analytic (rhAssembly evidence))
jointEvidenceYieldsRH evidence =
  Weil.dashiAssemblyImpliesRH (rhAssembly evidence)

------------------------------------------------------------------------
-- A finite countermodel to the INVALID generic inference:
--
--   odd irrationality witness => no off-line states.
--
-- The Boolean rational embedding is constant false while the three value
-- fields are constantly true. The finite irrationality witness is valid, yet
-- a one-point off-line state is inhabited. Nothing here is the real zeta.
------------------------------------------------------------------------

booleanCounterContext : Odd.ValueContext
booleanCounterContext = record
  { Value = Bool
  ; Rational = Bool
  ; embedRational = λ _ → false
  ; leanValue = λ _ → true
  ; bishopValue = λ _ → true
  ; dashiValue = λ _ → true
  ; leanToBishop = λ _ → refl
  ; bishopToDashi = λ _ → refl
  }

booleanOddWitness :
  Odd.OddIrrationalWitness booleanCounterContext
    (Odd.ValueContext.leanValue booleanCounterContext)
booleanOddWitness = zero , λ { (_ , ()) }

inhabitedOffLineSystem : Hermitian.EndgameSystem
inhabitedOffLineSystem = record
  { State = ⊤
  ; offLine = λ _ → ⊤
  }

genericOddWitnessCannotForceOffLineExclusion :
  ( (Odd.OddIrrationalWitness booleanCounterContext
         (Odd.ValueContext.leanValue booleanCounterContext))
    → (x : Hermitian.EndgameSystem.State inhabitedOffLineSystem)
    → Hermitian.EndgameSystem.offLine inhabitedOffLineSystem x
    → ⊥ ) → ⊥
genericOddWitnessCannotForceOffLineExclusion allegedCloser =
  allegedCloser booleanOddWitness tt tt
