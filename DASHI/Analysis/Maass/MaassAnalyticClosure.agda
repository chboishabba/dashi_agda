module DASHI.Analysis.Maass.MaassAnalyticClosure where

open import Agda.Primitive using (Setω)
open import Data.Product using (Σ; _,_)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Analysis.Maass.HejhalFibreContraction as HFC
import DASHI.Analysis.Maass.ValidatedNumericsArtifact as VNA
import DASHI.Analysis.Maass.ResidualToSpectralEnclosureTheorem as RSE

------------------------------------------------------------------------
-- Canonical Maaß closure package: carrier -> contraction -> validated
-- artifact -> residual-to-spectrum theorem.  No canonical instance is
-- exported until those inputs are actually supplied.

record MaassAnalyticClosure
  (Γ : MFC.ΓMaass)
  (Bytes Digest Payload GenuineForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm : Set)
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
    candidate : MSC.CandidateMaassForm Γ
    fibreContraction : HFC.HejhalFibreContraction Γ
    validatedArtifact :
      VNA.MaassValidatedNumericsArtifact
        (MSC.CandidateMaassForm.state candidate) Bytes Digest Payload
    spectralTheorem :
      RSE.MaassSpectralEnclosureTheorem candidate GenuineForm SpectralInterval Radius
        Cusp SpectralParameter ConstantTerm eigenvalueIn candidateWithin
        EisensteinFamily constantTerm constantTermIsZero continuousProjectionSmall
        windowAvoidsResidualSpectrum windowSeparatedFromContinuousSpectrum

certifiedForm :
  ∀ {Γ Bytes Digest Payload GenuineForm SpectralInterval Radius Cusp SpectralParameter
      ConstantTerm eigenvalueIn candidateWithin EisensteinFamily constantTerm
      constantTermIsZero continuousProjectionSmall windowAvoidsResidualSpectrum
      windowSeparatedFromContinuousSpectrum} →
  MaassAnalyticClosure Γ Bytes Digest Payload GenuineForm SpectralInterval Radius Cusp
    SpectralParameter ConstantTerm eigenvalueIn candidateWithin EisensteinFamily
    constantTerm constantTermIsZero continuousProjectionSmall
    windowAvoidsResidualSpectrum windowSeparatedFromContinuousSpectrum → GenuineForm
certifiedForm closure =
  Data.Product.proj₁
    (RSE.spectralInclusion (MaassAnalyticClosure.spectralTheorem closure))
