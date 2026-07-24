module DASHI.Physics.Closure.NSPeriodicStandardContinuumAdapter where

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSGalerkinCompactnessLimit as Limit
import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Galerkin
import DASHI.Physics.Closure.NSCompactGammaStandardAnalysisCompletion as Standard

------------------------------------------------------------------------
-- Adapter from the repository's existing G1--G19 Aubin--Lions/nonlinear-limit
-- certificate to the final vorticity/BKM lane.
--
-- Compactness, nonlinear passage, initial trace, Leray--Hopf identification,
-- compact-Gamma functional convergence, cutoff-estimate passage and selected
-- path identification are reused directly.  Only the genuinely stronger
-- cutoff-uniform vorticity estimate and its limit transport remain inputs.
------------------------------------------------------------------------

record StandardContinuumVorticityCompletion
    {ℓState ℓProp : Level}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp}
    (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) :
    Set (ℓState ⊔ ℓProp) where
  field
    CutoffVorticityIntegralFinite : Nat → Set ℓProp
    cutoffVorticityIntegralFinite : ∀ N → CutoffVorticityIntegralFinite N

    UniformVorticityIntegralBound : Set ℓProp
    cutoffUniformVorticity :
      (∀ N → CutoffVorticityIntegralFinite N) →
      UniformVorticityIntegralBound

    ContinuumVorticityIntegralFinite :
      Limit.SolutionClass (Galerkin.analytic S) → Set ℓProp

    vorticityIntegralPassesToLimit :
      UniformVorticityIntegralBound →
      ContinuumVorticityIntegralFinite
        (Galerkin.solution (Galerkin.g12 C))

    ContinuesBeyondSelectedInterval : Set ℓProp

    bkmContinuation :
      Limit.StrongSolution
        (Galerkin.analytic S)
        (Galerkin.solution (Galerkin.g12 C)) →
      ContinuumVorticityIntegralFinite
        (Galerkin.solution (Galerkin.g12 C)) →
      ContinuesBeyondSelectedInterval

open StandardContinuumVorticityCompletion public

standardLimitIsLerayHopf :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Limit.LerayHopfSolution
    (Galerkin.analytic S)
    (Galerkin.solution (Galerkin.g12 C))
standardLimitIsLerayHopf = Standard.limitSolvesNavierStokes

standardLimitIsStrongOnSelectedPath :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Limit.StrongSolution
    (Galerkin.analytic S)
    (Galerkin.solution (Galerkin.g12 C))
standardLimitIsStrongOnSelectedPath C =
  Galerkin.repositoryStrong (Galerkin.g19 C)

standardSelectedPathIdentified :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.SelectedPathIdentified S
standardSelectedPathIdentified =
  Standard.weakStrongUniquenessIdentifiesSelectedPath

standardCompactGammaCutoffEstimatePasses :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  Galerkin.CutoffEstimatePasses
    S
    (Galerkin.subsequence (Galerkin.g5 C))
    (Galerkin.shell (Galerkin.g13 C))
standardCompactGammaCutoffEstimatePasses =
  Standard.differentialInequalityPassesToLimit

standardContinuumVorticityIntegralFinite :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (V : StandardContinuumVorticityCompletion C) →
  ContinuumVorticityIntegralFinite V
    (Galerkin.solution (Galerkin.g12 C))
standardContinuumVorticityIntegralFinite C V =
  vorticityIntegralPassesToLimit V
    (cutoffUniformVorticity V (cutoffVorticityIntegralFinite V))

standardContinuumBKMContinuation :
  ∀ {ℓState ℓProp}
    {S : Galerkin.ConcreteGalerkinSetting ℓState ℓProp} →
  (C : Galerkin.ConcreteAubinLionsNonlinearLimitCertificate S) →
  (V : StandardContinuumVorticityCompletion C) →
  ContinuesBeyondSelectedInterval V
standardContinuumBKMContinuation C V =
  bkmContinuation V
    (standardLimitIsStrongOnSelectedPath C)
    (standardContinuumVorticityIntegralFinite C V)
