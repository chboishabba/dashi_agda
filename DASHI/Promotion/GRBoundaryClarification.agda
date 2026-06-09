module DASHI.Promotion.GRBoundaryClarification where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Promotion.ClassicalFieldObligations as Classical

------------------------------------------------------------------------
-- GR promotion authority boundary clarification.
--
-- This module refines the existing classical-field GR obligation lane
-- without promoting GR.  It separates the bounded flat/Minkowski recovery
-- that may be treated internally from continuum non-flat GR claims that
-- still require external mathematical/physical authority and adapters.

data GRClarifiedScope : Set where
  minkowskiFlatRecoveryScope : GRClarifiedScope
  flatTangentSpaceRecoveryScope : GRClarifiedScope
  nonFlatEinsteinEquationScope : GRClarifiedScope
  bianchiContinuumIdentityScope : GRClarifiedScope
  stressEnergySourceCouplingScope : GRClarifiedScope
  schwarzschildContinuumScope : GRClarifiedScope
  cosmologyContinuumScope : GRClarifiedScope
  continuumGRTheoryScope : GRClarifiedScope

data GRBoundaryStatus : Set where
  internalBoundedRecovery : GRBoundaryStatus
  continuumAuthorityBlocked : GRBoundaryStatus
  adapterAndAuthorityBlocked : GRBoundaryStatus
  promotionBlocked : GRBoundaryStatus

record GRBoundaryRow : Set where
  field
    scope : GRClarifiedScope
    boundaryStatus : GRBoundaryStatus
    positiveBoundary : String
    preciseMissingObligation : String
    allowedInternalUse : Bool
    allowedInternalUseProof : allowedInternalUse ≡ true
    promotesGR : Bool
    promotesGRIsFalse : promotesGR ≡ false

open GRBoundaryRow public

mkInternalBoundedRow :
  GRClarifiedScope →
  String →
  String →
  GRBoundaryRow
mkInternalBoundedRow scope positive missing =
  record
    { scope = scope
    ; boundaryStatus = internalBoundedRecovery
    ; positiveBoundary = positive
    ; preciseMissingObligation = missing
    ; allowedInternalUse = true
    ; allowedInternalUseProof = refl
    ; promotesGR = false
    ; promotesGRIsFalse = refl
    }

mkBlockedRow :
  GRClarifiedScope →
  GRBoundaryStatus →
  String →
  String →
  GRBoundaryRow
mkBlockedRow scope status positive missing =
  record
    { scope = scope
    ; boundaryStatus = status
    ; positiveBoundary = positive
    ; preciseMissingObligation = missing
    ; allowedInternalUse = true
    ; allowedInternalUseProof = refl
    ; promotesGR = false
    ; promotesGRIsFalse = refl
    }

canonicalGRBoundaryRows : List GRBoundaryRow
canonicalGRBoundaryRows =
  mkInternalBoundedRow
    minkowskiFlatRecoveryScope
    "Minkowski metric, flat signature bookkeeping, and zero-curvature recovery may be used as a bounded internal known-limit adapter."
    "Missing before promotion: proof that flat recovery extends to non-flat Levi-Civita curvature, Einstein tensor dynamics, source coupling, and continuum solution classes."
  ∷ mkInternalBoundedRow
    flatTangentSpaceRecoveryScope
    "Local flat tangent-space or bounded weak-field bookkeeping may be internal when explicitly scoped to recovery and not to full GR."
    "Missing before promotion: controlled continuum limit from bounded/local flat recovery to global Lorentzian manifolds with nonzero curvature and physical observables."
  ∷ mkBlockedRow
    nonFlatEinsteinEquationScope
    adapterAndAuthorityBlocked
    "Non-flat Einstein field equations are named as the target equation only."
    "Missing obligation: continuum authority token plus adapter proving G_mu_nu + Lambda g_mu_nu = (8 pi G / c^4) T_mu_nu for non-flat Lorentzian metrics with explicit units and boundary conditions."
  ∷ mkBlockedRow
    bianchiContinuumIdentityScope
    continuumAuthorityBlocked
    "Contracted Bianchi identity is recorded as required continuum authority, not derived here."
    "Missing obligation: accepted differential-geometric authority/proof for nabla_mu G^{mu nu} = 0 on the continuum carrier and compatibility with the chosen connection conventions."
  ∷ mkBlockedRow
    stressEnergySourceCouplingScope
    adapterAndAuthorityBlocked
    "Stress-energy/source coupling is a named bridge between matter models and curvature only."
    "Missing obligation: matter-model-to-T_mu_nu adapter, conservation compatibility nabla_mu T^{mu nu} = 0, normalization authority for G and c, and empirical source calibration."
  ∷ mkBlockedRow
    schwarzschildContinuumScope
    adapterAndAuthorityBlocked
    "Schwarzschild/asymptotically flat solution claims remain outside the internal flat recovery boundary."
    "Missing obligation: continuum solution authority for Schwarzschild geometry, exterior-domain assumptions, horizon/singularity boundary treatment, and observable adapter."
  ∷ mkBlockedRow
    cosmologyContinuumScope
    adapterAndAuthorityBlocked
    "Cosmology claims remain authority/adapter blocked."
    "Missing obligation: FLRW or alternate cosmological model authority, stress-energy equation-of-state adapter, Lambda convention, redshift-distance observable map, and empirical calibration."
  ∷ mkBlockedRow
    continuumGRTheoryScope
    promotionBlocked
    "Continuum GR as a theory remains an external authority surface."
    "Missing obligation: full continuum manifold, tensor calculus, covariance, field-equation, solution-family, source, unit, and empirical-observable authority package."
  ∷ []

listLength : {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

canonicalInternalBoundedRows : List GRBoundaryRow
canonicalInternalBoundedRows =
  mkInternalBoundedRow
    minkowskiFlatRecoveryScope
    "Minkowski/flat recovery is internal only under bounded known-limit scope."
    "Missing all non-flat continuum GR promotion obligations."
  ∷ mkInternalBoundedRow
    flatTangentSpaceRecoveryScope
    "Flat tangent-space recovery is internal only under bounded local scope."
    "Missing global continuum and nonzero-curvature promotion obligations."
  ∷ []

canonicalAuthorityBlockedRows : List GRBoundaryRow
canonicalAuthorityBlockedRows =
  mkBlockedRow
    nonFlatEinsteinEquationScope
    adapterAndAuthorityBlocked
    "Non-flat Einstein equations remain blocked."
    "Missing continuum EFE authority and adapter."
  ∷ mkBlockedRow
    bianchiContinuumIdentityScope
    continuumAuthorityBlocked
    "Bianchi identity remains continuum-authority blocked."
    "Missing continuum contracted-Bianchi authority."
  ∷ mkBlockedRow
    stressEnergySourceCouplingScope
    adapterAndAuthorityBlocked
    "Stress-energy/source coupling remains blocked."
    "Missing matter-source adapter and conservation compatibility."
  ∷ mkBlockedRow
    schwarzschildContinuumScope
    adapterAndAuthorityBlocked
    "Schwarzschild solution claims remain blocked."
    "Missing continuum solution authority and observable adapter."
  ∷ mkBlockedRow
    cosmologyContinuumScope
    adapterAndAuthorityBlocked
    "Cosmology claims remain blocked."
    "Missing cosmological model authority and redshift-distance adapter."
  ∷ mkBlockedRow
    continuumGRTheoryScope
    promotionBlocked
    "Continuum GR promotion remains blocked."
    "Missing full continuum GR authority package."
  ∷ []

record GRBoundaryClarificationIndex : Set₁ where
  field
    sourceClassicalGRReceipt :
      Classical.GRFieldEquationPromotionObligation
    clarifiedRows : List GRBoundaryRow
    internalBoundedRows : List GRBoundaryRow
    blockedAuthorityRows : List GRBoundaryRow
    validationCommand : String
    grPromotion : Bool
    grPromotionIsFalse : grPromotion ≡ false
    sourceClassicalGRPromotionIsFalse :
      Classical.GRFieldEquationPromotionObligation.grFieldEquationPromoted
        sourceClassicalGRReceipt
      ≡ false

open GRBoundaryClarificationIndex public

canonicalGRBoundaryClarificationIndex :
  GRBoundaryClarificationIndex
canonicalGRBoundaryClarificationIndex = record
  { sourceClassicalGRReceipt =
      Classical.canonicalGRFieldEquationPromotionObligation
  ; clarifiedRows = canonicalGRBoundaryRows
  ; internalBoundedRows = canonicalInternalBoundedRows
  ; blockedAuthorityRows = canonicalAuthorityBlockedRows
  ; validationCommand =
      "agda -i . DASHI/Promotion/GRBoundaryClarification.agda"
  ; grPromotion = false
  ; grPromotionIsFalse = refl
  ; sourceClassicalGRPromotionIsFalse = refl
  }

canonicalGRBoundaryRowCountIs8 :
  listLength
    (GRBoundaryClarificationIndex.clarifiedRows
      canonicalGRBoundaryClarificationIndex)
  ≡ 8
canonicalGRBoundaryRowCountIs8 = refl

canonicalGRInternalBoundedRowCountIs2 :
  listLength
    (GRBoundaryClarificationIndex.internalBoundedRows
      canonicalGRBoundaryClarificationIndex)
  ≡ 2
canonicalGRInternalBoundedRowCountIs2 = refl

canonicalGRAuthorityBlockedRowCountIs6 :
  listLength
    (GRBoundaryClarificationIndex.blockedAuthorityRows
      canonicalGRBoundaryClarificationIndex)
  ≡ 6
canonicalGRAuthorityBlockedRowCountIs6 = refl

canonicalGRPromotionIsFalse :
  GRBoundaryClarificationIndex.grPromotion
    canonicalGRBoundaryClarificationIndex
  ≡ false
canonicalGRPromotionIsFalse = refl

canonicalSourceClassicalGRPromotionIsFalse :
  Classical.GRFieldEquationPromotionObligation.grFieldEquationPromoted
    (GRBoundaryClarificationIndex.sourceClassicalGRReceipt
      canonicalGRBoundaryClarificationIndex)
  ≡ false
canonicalSourceClassicalGRPromotionIsFalse = refl
