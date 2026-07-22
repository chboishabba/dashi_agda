module DASHI.Foundations.EMLPositiveRealAnalyticPackage where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _-ℝ_)
open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- Concrete carrier, explicit external transcendental authority.
--
-- DASHI's canonical real carrier is axiomatic.  This module therefore fixes the
-- actual carrier and subtraction operation to that authority boundary, while
-- requiring the positive-domain exp/log identities and all compiler-introduced
-- definedness facts as a named package.  No global logarithm identity is hidden.

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

    ExpAdmissibleR : ℝ → Set
    LogAdmissibleR : ℝ → Set
    SubAdmissibleR : ℝ → ℝ → Set

    compilerDefinednessR :
      let M = record
            { Carrier = ℝ
            ; one = 1ℝ
            ; exp = expR
            ; log = logR
            ; sub = _-ℝ_
            }
          D = record
            { ExpAdmissible = ExpAdmissibleR
            ; LogAdmissible = LogAdmissibleR
            ; SubAdmissible = SubAdmissibleR
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
    { ExpAdmissible = ExpAdmissibleR A
    ; LogAdmissible = LogAdmissibleR A
    ; SubAdmissible = SubAdmissibleR A
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
    { laws = positiveRealCompilerLaws A
    ; admissibility = positiveRealAdmissibility A
    ; compilerDefinedness = compilerDefinednessR A
    }
