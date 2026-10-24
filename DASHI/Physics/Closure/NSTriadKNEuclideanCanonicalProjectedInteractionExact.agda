module DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalProjectedInteractionExact where

------------------------------------------------------------------------
-- A / CANONICAL WHOLE-SPACE PROJECTED INTERACTION CONSTRUCTOR
--
-- The original EuclideanProjectedInteraction surface deliberately left the
-- raw Fourier cell and Leray projection behind opaque meaning fields.  Once
-- the continuous divergence-form and canonical Bishop Leray owners exist,
-- there is no reason for the canonical A realization to keep those formulas
-- abstract.
--
-- Given a punctured output frequency and a continuous convolution interaction
-- whose output is that frequency, construct the physical interaction directly:
--
--   u_eta  = u^(t,eta)
--   u_zeta = u^(t,zeta)
--   raw    = i (xi . u_eta) u_zeta
--   proj   = P_xi raw.
--
-- The downstream ProjectedInteractionFormulaWeld is therefore produced with
-- no analytic or representation hypothesis beyond the output-frequency
-- identification itself.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 2026-10-24 A PHYSICAL SAME-OBJECT FOURIER MAX-CUT
--
-- The local raw divergence-form/Leray cell below is ALREADY implemented.
-- The remaining transform is not another pointwise projector identity:
-- construct the SPATIAL Fourier/Plancherel map on the SAME continuum
-- physical velocity (not a free FourierTransformVelocity : Set).
--
-- Standard finite-energy distributional identity:
--   F[(u.grad)u]_i(xi) =
--     i (2pi)^(-3) sum_j xi_j int_eta uhat_j(eta) uhat_i(xi-eta)
-- for div u=0; initially Schwartz, then u in L2 via
-- u_i u_j in L1, L2 approximation and distribution derivatives.
--
-- Physical source estimate for u in H1(R3):
-- |F[P div(u tensor u)](xi)|
--   <= min( |xi| E, sqrt(E D)),
-- E=||u||_2^2, D=||grad u||_2^2.
-- The *direct* heat-inverse response is globally L2 in frequency:
-- integral |source/(nu|xi|^2)|^2
--   <= 8pi E^(3/2) sqrt(D) / nu^2.
-- This is standard analysis documented in the live NSProofControl roadmap.
-- It has NOT yet been transported into Bishop Fourier formal semantics,
-- nor paid the signed centered-resolvent A2/A3 continuation theorem.
-- Exact nontrivial Schwartz provenance/witness:
-- scripts/ns_a_schwartz_fourier_same_object.py.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSCanonicalEuclideanPeriodicSemanticCarriersExact as Canonical
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanPhysicalFourierNSExact as Physical
import DASHI.Physics.Closure.NSTriadKNEuclideanDivergenceFormOutputFactorExact as Output
import DASHI.Physics.Closure.NSTriadKNEuclideanViscousHeatRateExact as Heat
import DASHI.Physics.Closure.NSTriadKNEuclideanBishopLerayPythagorasExact as Leray
import DASHI.Physics.Closure.NSTriadKNEuclideanCanonicalLerayProjectionExact as CanonicalLeray
import DASHI.Physics.Closure.NSTriadKNEuclideanProjectedInteractionQWeldExact as Weld

-- A simpler definitionally transparent constructor.  Keeping the meaning
-- fields at reflexive propositions avoids assigning independent authority to
-- formulas that are already the definitions of the canonical interaction.
canonicalProjectedInteraction :
  ∀ {S : Canonical.CanonicalNSSemantics} →
  (trajectory : Physical.EuclideanFourierTrajectory S) →
  (point : Heat.PuncturedEuclideanFrequency) →
  (interaction : Euclidean.EuclideanInteraction) →
  Euclidean.xi interaction ≡ Heat.frequency point →
  Canonical.Time →
  Physical.EuclideanProjectedInteraction trajectory
canonicalProjectedInteraction trajectory point interaction outputExact time =
  let
    uEta =
      Physical.velocityHat trajectory time (Euclidean.eta interaction)
    uZeta =
      Physical.velocityHat trajectory time (Euclidean.zeta interaction)
    raw =
      Output.divergenceFormRawCell
        (Heat.frequency point)
        uEta uZeta
    projected =
      Leray.lerayProject
        (Heat.frequency point)
        (CanonicalLeray.canonicalLerayInverse point)
        raw
  in
  record
    { Physical.interaction = interaction
    ; Physical.time = time
    ; Physical.uEta = uEta
    ; Physical.uEtaExact = refl
    ; Physical.uZeta = uZeta
    ; Physical.uZetaExact = refl
    ; Physical.rawConvolutionCell = raw
    ; Physical.lerayProjectedCell = projected
    ; Physical.RawInteractionMeaning = raw ≡ raw
    ; Physical.LerayProjectionMeaning = projected ≡ projected
    ; Physical.rawInteractionExact = refl
    ; Physical.lerayProjectionExact = refl
    }

canonicalProjectedInteractionFormulaWeld :
  ∀ {S : Canonical.CanonicalNSSemantics}
    {trajectory : Physical.EuclideanFourierTrajectory S}
    {point : Heat.PuncturedEuclideanFrequency}
    {interaction : Euclidean.EuclideanInteraction}
    (outputExact : Euclidean.xi interaction ≡ Heat.frequency point)
    (time : Canonical.Time) →
  Weld.ProjectedInteractionFormulaWeld
    point
    (canonicalProjectedInteraction
      trajectory point interaction outputExact time)
canonicalProjectedInteractionFormulaWeld outputExact time =
  record
    { Weld.outputIsPointFrequency = outputExact
    ; Weld.rawCellIsDivergenceForm = refl
    ; Weld.projectedCellIsCanonicalLeray = refl
    }

canonicalProjectedInteractionConstructed : Bool
canonicalProjectedInteractionConstructed = true

canonicalRawFormulaRequiresIndependentAuthority : Bool
canonicalRawFormulaRequiresIndependentAuthority = false

canonicalLerayFormulaRequiresIndependentAuthority : Bool
canonicalLerayFormulaRequiresIndependentAuthority = false

clayPromotion : Bool
clayPromotion = false

canonicalProjectedInteractionConstructedIsTrue :
  canonicalProjectedInteractionConstructed ≡ true
canonicalProjectedInteractionConstructedIsTrue = refl

canonicalRawFormulaRequiresIndependentAuthorityIsFalse :
  canonicalRawFormulaRequiresIndependentAuthority ≡ false
canonicalRawFormulaRequiresIndependentAuthorityIsFalse = refl

canonicalLerayFormulaRequiresIndependentAuthorityIsFalse :
  canonicalLerayFormulaRequiresIndependentAuthority ≡ false
canonicalLerayFormulaRequiresIndependentAuthorityIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
