module DASHI.Companions.MaassCategoricalLoom where

open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Core.GrammarGeneratedCategory as GGC
import DASHI.Core.ProjectionHomology as PH
import DASHI.Core.ProjectionCategory as PC

maassGrammarCategory : GGC.GrammarGeneratedCategory
maassGrammarCategory = record
  { Grammar = MFC.ΓMaass
  ; 𝓟 = λ _ → MSC.maassProjectionCategory
  ; grammarReading = "Gamma_Maass: group, weight, spectral parameter, N, Q, y, generators, tail bounds"
  }

-- Persistence is a certification claim made under a grammar transport, not a
-- statement that arbitrary numerical reconstructions are equivalent.
maassProjectionHomology : PH.ProjectionHomology maassGrammarCategory
maassProjectionHomology = record
  { GrammarMorphism = λ _ _ → String
  ; TransportFunctor = λ _ → MSC.maassProjectionCategory
  ; transportPreservesId = λ _ x → x
  ; transportPreservesHom = λ _ f → f
  ; HomologySet = λ _ → String
  ; persists = λ _ _ _ → ⊤
  ; homologyReading = "Maaß persistence: parity, isolation, certified eigenvalue, coefficient bounds, Hecke relations."
  }

