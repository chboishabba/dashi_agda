module DASHI.Foundations.EMLPositiveRealAnalyticPackage where

open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _-ℝ_)
open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- Concrete carrier, explicit external transcendental authority.
--
-- DASHI's canonical real carrier is axiomatic.  This module fixes the actual
-- carrier and subtraction operation to that authority boundary.  Real exp and
-- subtraction are treated as total; logarithm definedness is exactly positivity.
-- Both semantic laws and compiler-introduced closure are required only on that
-- certified domain, not as false global logarithm identities.

data Always : Set where
  always : Always

record PositiveRealTranscendentalAuthority : Set₁ where
  field
    expR logR : ℝ → ℝ
    Positive : ℝ → Set

    onePositive : Positive 1ℝ
    expPositive : ∀ x → Positive (expR x)

    compilerDefinednessR :
      let M = record
            { Carrier = ℝ
            ; one = 1ℝ
            ; exp = expR
            ; log = logR
            ; sub = _-ℝ_
            }
          D = record
            { ExpAdmissible = λ _ → Always
            ; LogAdmissible = Positive
            ; SubAdmissible = λ _ _ → Always
            }
      in EMLCompilerDefinedness M D

    compilerLawsOnDomainR :
      let M = record
            { Carrier = ℝ
            ; one = 1ℝ
            ; exp = expR
            ; log = logR
            ; sub = _-ℝ_
            }
          D = record
            { ExpAdmissible = λ _ → Always
            ; LogAdmissible = Positive
            ; SubAdmissible = λ _ _ → Always
            }
      in EMLCompilerLawsOnDomain M D

open PositiveRealTranscendentalAuthority public

positiveRealEMLModel :
  PositiveRealTranscendentalAuthority →
  ExpLogSubModel
positiveRealEMLModel A =
  record
    { Carrier = ℝ
    ; one = 1ℝ
    ; exp = expR A
    ; log = logR A
    ; sub = _-ℝ_
    }

positiveRealAdmissibility :
  (A : PositiveRealTranscendentalAuthority) →
  EMLAdmissibility (positiveRealEMLModel A)
positiveRealAdmissibility A =
  record
    { ExpAdmissible = λ _ → Always
    ; LogAdmissible = Positive A
    ; SubAdmissible = λ _ _ → Always
    }

positiveRealAnalyticPackage :
  (A : PositiveRealTranscendentalAuthority) →
  AnalyticEMLCompilerPackage (positiveRealEMLModel A)
positiveRealAnalyticPackage A =
  record
    { admissibility = positiveRealAdmissibility A
    ; compilerDefinedness = compilerDefinednessR A
    ; compilerLawsOnDomain = compilerLawsOnDomainR A
    }
