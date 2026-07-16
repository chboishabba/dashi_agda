module DASHI.Analysis.MaassSpectralCertification where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Agda.Builtin.Equality using (refl)
open import Agda.Builtin.Sigma using (_,_)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.RootsOfUnitySampling as ROS
import DASHI.Analysis.HejhalAutomorphyResidual as HAR
import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ResidualNaturality as RN

------------------------------------------------------------------------
-- This legacy candidate/certified surface records the old closure vocabulary.
-- It is not the analytic certificate: its ⊤ fields do not establish spectral
-- inclusion.  The theorem-critical owner is now
-- Analysis.Maass.ResidualToSpectralEnclosureTheorem, assembled by
-- Analysis.Maass.MaassAnalyticClosure.  Hejhal's finite system alone supplies
-- neither inclusion nor uniqueness, hence there is intentionally no canonical
-- CertifiedMaassForm inhabitant here.

record CandidateMaassForm (Γ : MFC.ΓMaass) : Set where
  field
    state     : MFC.TruncatedFourierState Γ
    comparison : MFC.AutomorphyComparison Γ

record MaassClosed (Γ : MFC.ΓMaass) (candidate : CandidateMaassForm Γ) : Set where
  field
    samplingExact          : ROS.ExactTruncatedRecovery Γ (CandidateMaassForm.state candidate)
    residualEnclosure      : HAR.ResidualEnclosure Γ (CandidateMaassForm.state candidate)
    automorphyClosed       : ⊤
    tailClosed             : ⊤
    spectralIsolation      : ⊤
    certificationRadiusBelowIsolation : ⊤

record CertifiedMaassForm (Γ : MFC.ΓMaass) : Set where
  field
    candidate : CandidateMaassForm Γ
    closed    : MaassClosed Γ candidate
    certificateReading : String

data MaassObject : Set where
  candidateObject certifiedObject : MaassObject

Underlying : MaassObject → Set
Underlying candidateObject = ∀ Γ → CandidateMaassForm Γ
Underlying certifiedObject = ∀ Γ → CertifiedMaassForm Γ

maassProjectionCategory : PC.ProjectionCategory
maassProjectionCategory = record
  { Obj = MaassObject
  ; Hom = λ A B → Underlying A → Underlying B
  ; id = λ x → x
  ; _∘_ = λ g f x → g (f x)
  ; id-left = λ f → refl
  ; id-right = λ f → refl
  ; assoc = λ f g h → refl
  ; categoryReading = "Pi_Maass(candidate/certified analytic surfaces)"
  }

-- The generic residual machinery is instantiated with the structured
-- residual.  The authority comparison is still supplied per candidate.
maassResidualNaturality : RN.ResidualNaturality maassProjectionCategory maassProjectionCategory
maassResidualNaturality = record
  { FObj = λ x → x
  ; FHom = λ f → f
  ; F-id = refl
  ; F-comp = λ _ _ → refl
  ; residual = λ _ _ → HAR.MaassResidual
  ; closed = λ _ _ → HAR.MaassResidual
  ; residualReading = "Maaß residual: sampling, automorphy, Laplace, cusp, truncation, normalisation, Hecke"
  }

-- A concrete PromotionTransformation is intentionally not manufactured here:
-- its identity law would require an analytic residual certificate even for the
-- abstract identity map.  A specific authority comparison supplies that
-- instance only after its zero/bounded residual proof is available.
