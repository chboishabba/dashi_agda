module DASHI.Analysis.Maass.CuspContinuousSpectrumSeparation where

open import Agda.Primitive using (Setω)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC

------------------------------------------------------------------------
-- A Maaß cusp-form enclosure is not justified by a small Laplace residual
-- alone: the continuous Eisenstein spectrum and any residual spectrum must
-- be excluded in the claimed window.  This is deliberately a theorem input,
-- not a Boolean gate or a numerical receipt.

record CuspContinuousSpectrumSeparation
  {Γ : MFC.ΓMaass}
  (candidate : MSC.CandidateMaassForm Γ)
  (Cusp SpectralParameter ConstantTerm SpectralInterval : Set)
  (EisensteinFamily : Cusp → SpectralParameter → Set)
  (constantTerm : MSC.CandidateMaassForm Γ → Cusp → ConstantTerm)
  (constantTermIsZero : ConstantTerm → Set)
  (continuousProjectionSmall : MSC.CandidateMaassForm Γ → Set)
  (windowAvoidsResidualSpectrum : SpectralInterval → Set)
  (windowSeparatedFromContinuousSpectrum : SpectralInterval → Set)
  : Setω where
  field
    cusps : Cusp → Set
    eisensteinFamily : ∀ cusp → cusps cusp → ∀ s → EisensteinFamily cusp s
    candidateConstantTermsVanish :
      ∀ cusp → cusps cusp → constantTermIsZero (constantTerm candidate cusp)
    continuousProjectionBound : continuousProjectionSmall candidate
    residualSpectrumExcluded : ∀ window → windowAvoidsResidualSpectrum window
    continuousSpectrumExcluded :
      ∀ window → windowSeparatedFromContinuousSpectrum window

open CuspContinuousSpectrumSeparation public
