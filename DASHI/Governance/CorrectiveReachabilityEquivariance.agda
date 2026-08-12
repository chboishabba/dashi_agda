module DASHI.Governance.CorrectiveReachabilityEquivariance where

open import Data.Empty using (⊥)
import DASHI.Governance.AsymmetricReflectionPropositionLocality as Reflection

------------------------------------------------------------------------
-- Future reclassification language.
--
-- Equal treatment is not "same outcome".  It is access to corresponding
-- correction/reclassification paths under equivalent evidentiary traces.
------------------------------------------------------------------------

record PairedCorrectiveLanguage
    (C : Reflection.CorrectiveReachabilitySystem) : Set₁ where
  field
    insideActor outsideActor : Reflection.Actor C
    Trace : Set
    InsideClass : Set
    OutsideClass : Set

    insideClass : InsideClass → Reflection.Classification C insideActor
    outsideClass : OutsideClass → Reflection.Classification C outsideActor

    translateTrace : Trace → Trace
    translateClass : OutsideClass → InsideClass

    insideReachable : Trace → InsideClass → Set
    outsideReachable : Trace → OutsideClass → Set

open PairedCorrectiveLanguage public

------------------------------------------------------------------------
-- Role-equivariance at the future-language level: an admissible correction
-- path for the outside actor transports to the corresponding inside path.
-- This does not force equal classifications or equal material outcomes.
------------------------------------------------------------------------

record RoleEquivariantCorrectiveAccess
    {C : Reflection.CorrectiveReachabilitySystem}
    (L : PairedCorrectiveLanguage C) : Set₁ where
  field
    outsideToInside :
      ∀ {trace classification} →
      outsideReachable L trace classification →
      insideReachable L
        (translateTrace L trace)
        (translateClass L classification)

open RoleEquivariantCorrectiveAccess public

------------------------------------------------------------------------
-- Constructive asymmetry witness: a corresponding correction is reachable for
-- the outside actor while the matched inside route is blocked.
------------------------------------------------------------------------

record AsymmetricCorrectiveAccessWitness
    {C : Reflection.CorrectiveReachabilitySystem}
    (L : PairedCorrectiveLanguage C) : Set₁ where
  field
    trace : Trace L
    classification : OutsideClass L
    outsidePath : outsideReachable L trace classification
    insideBlocked :
      insideReachable L
        (translateTrace L trace)
        (translateClass L classification) →
      ⊥

open AsymmetricCorrectiveAccessWitness public

roleEquivarianceRefutesCorrectiveAsymmetry :
  ∀ {C} {L : PairedCorrectiveLanguage C} →
  RoleEquivariantCorrectiveAccess L →
  AsymmetricCorrectiveAccessWitness L →
  ⊥
roleEquivarianceRefutesCorrectiveAsymmetry equivariance witness =
  insideBlocked witness
    (outsideToInside equivariance (outsidePath witness))

------------------------------------------------------------------------
-- Symmetric evidentiary access is deliberately weaker than equal policy
-- result.  Material power, causal responsibility, injury and remedy magnitude
-- remain coordinates of the application state.
------------------------------------------------------------------------

data CorrectiveEquivarianceAutomaticallyEqualOutcome
    {C : Reflection.CorrectiveReachabilitySystem}
    {L : PairedCorrectiveLanguage C}
    (e : RoleEquivariantCorrectiveAccess L) : Set where

correctiveEquivarianceDoesNotForceEqualOutcome :
  ∀ {C} {L : PairedCorrectiveLanguage C}
    {e : RoleEquivariantCorrectiveAccess L} →
  CorrectiveEquivarianceAutomaticallyEqualOutcome e → ⊥
correctiveEquivarianceDoesNotForceEqualOutcome ()
