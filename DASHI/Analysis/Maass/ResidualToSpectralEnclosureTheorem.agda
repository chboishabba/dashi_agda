module DASHI.Analysis.Maass.ResidualToSpectralEnclosureTheorem where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Product using (Σ; _×_)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Analysis.Maass.ValidatedNumericsArtifact as VNA
import DASHI.Analysis.Maass.CuspContinuousSpectrumSeparation as CCS

------------------------------------------------------------------------
-- The theorem-critical implication.  All analytic notions are explicit
-- parameters so a concrete interval/Bessel implementation can state the
-- genuine result rather than replacing it with a status Boolean.

record MaassSpectralEnclosureTheorem
  {Γ : MFC.ΓMaass}
  (candidate : MSC.CandidateMaassForm Γ)
  (GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm : Set)
  (eigenvalueIn : GenuineForm → SpectralInterval → Set)
  (candidateWithin : MSC.CandidateMaassForm Γ → GenuineForm → Radius → Set)
  (EisensteinFamily : Cusp → SpectralParameter → Set)
  (constantTerm : MSC.CandidateMaassForm Γ → Cusp → ConstantTerm)
  (constantTermIsZero : ConstantTerm → Set)
  (continuousProjectionSmall : MSC.CandidateMaassForm Γ → Set)
  (windowAvoidsResidualSpectrum : SpectralInterval → Set)
  (windowSeparatedFromContinuousSpectrum : SpectralInterval → Set)
  : Setω where
  field
    validatedBounds : VNA.MaassAnalyticBounds Γ (MSC.CandidateMaassForm.state candidate)
    spectralWindow : SpectralInterval
    isolationRadius : Radius
    residualInsideWindowRadius : Set
    cuspContinuousSeparation :
      CCS.CuspContinuousSpectrumSeparation candidate Cusp SpectralParameter ConstantTerm
        SpectralInterval EisensteinFamily constantTerm constantTermIsZero
        continuousProjectionSmall windowAvoidsResidualSpectrum
        windowSeparatedFromContinuousSpectrum
    spectralInclusion :
      Σ GenuineForm (λ f →
        eigenvalueIn f spectralWindow × candidateWithin candidate f isolationRadius)
    uniquenessInWindow :
      ∀ f g → eigenvalueIn f spectralWindow → eigenvalueIn g spectralWindow → f ≡ g

open MaassSpectralEnclosureTheorem public
