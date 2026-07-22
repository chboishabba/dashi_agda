module DASHI.Foundations.EMLPositiveRealAnalyticPackage where

open import Agda.Builtin.Equality using (_≡_)

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
-- The remaining field is the genuine closure theorem for compiler-introduced
-- intermediate values.

data Always : Set where
  always : Always

record PositiveRealTranscendentalAuthority : Set₁ where
  field
    expR logR : ℝ → ℝ
    Positive : ℝ → Set

    onePositive : Positive 1ℝ
    expPositive : ∀ x → Positive (expR x)

    expEncodingLaw :
      ∀ x →
      (expR x -ℝ logR 1ℝ) ≡ expR x

    logEncodingLaw :
      ∀ x →
      (expR 1ℝ -ℝ
        logR
          (expR
            (expR 1ℝ -ℝ logR x)
           -ℝ logR 1ℝ))
      ≡ logR x

    subEncodingLaw :
      ∀ x y →
      (expR
        (expR 1ℝ -ℝ
          logR
            (expR
              (expR 1ℝ -ℝ logR x)
             -ℝ logR 1ℝ))
       -ℝ
       logR (expR y -ℝ logR 1ℝ))
      ≡ x -ℝ y

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

positiveRealCompilerLaws :
  (A : PositiveRealTranscendentalAuthority) →
  EMLCompilerLaws (positiveRealEMLModel A)
positiveRealCompilerLaws A =
  record
    { expEncoding = expEncodingLaw A
    ; logEncoding = logEncodingLaw A
    ; subEncoding = subEncodingLaw A
    }

positiveRealAnalyticPackage :
  (A : PositiveRealTranscendentalAuthority) →
  AnalyticEMLCompilerPackage (positiveRealEMLModel A)
positiveRealAnalyticPackage A =
  record
    { admissibility = positiveRealAdmissibility A
    ; compilerDefinedness = compilerDefinednessR A
    ; compilerLawsOnDomain =
        globalLawsGiveDomainLaws (positiveRealCompilerLaws A)
    }
