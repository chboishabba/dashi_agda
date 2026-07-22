module DASHI.Foundations.EMLComplexBranchPackage where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- A logarithm branch is data, not an ambient global convention.  The exact
-- EML identities are required only together with the branch/domain closure
-- which makes every introduced logarithm legitimate.

record ComplexLogBranchAuthority : Set₁ where
  field
    Complex : Set
    oneC : Complex
    expC logC : Complex → Complex
    subC : Complex → Complex → Complex

    BranchDomain : Complex → Set
    PrincipalStrip : Complex → Set

    oneInBranch : BranchDomain oneC
    expInBranch : ∀ z → PrincipalStrip z → BranchDomain (expC z)

    expLogOnBranch :
      ∀ z →
      BranchDomain z →
      expC (logC z) ≡ z

    logExpOnStrip :
      ∀ z →
      PrincipalStrip z →
      logC (expC z) ≡ z

    expEncodingLawC :
      ∀ z →
      subC (expC z) (logC oneC) ≡ expC z

    logEncodingLawC :
      ∀ z →
      subC
        (expC oneC)
        (logC
          (subC
            (expC (subC (expC oneC) (logC z)))
            (logC oneC)))
      ≡ logC z

    subEncodingLawC :
      ∀ z w →
      subC
        (expC
          (subC
            (expC oneC)
            (logC
              (subC
                (expC (subC (expC oneC) (logC z)))
                (logC oneC)))))
        (logC (subC (expC w) (logC oneC)))
      ≡ subC z w

    ExpAdmissibleC : Complex → Set
    LogAdmissibleC : Complex → Set
    SubAdmissibleC : Complex → Complex → Set

    compilerDefinednessC :
      let M = record
            { Carrier = Complex
            ; one = oneC
            ; exp = expC
            ; log = logC
            ; sub = subC
            }
          D = record
            { ExpAdmissible = ExpAdmissibleC
            ; LogAdmissible = LogAdmissibleC
            ; SubAdmissible = SubAdmissibleC
            }
      in EMLCompilerDefinedness M D

open ComplexLogBranchAuthority public

complexBranchEMLModel :
  ComplexLogBranchAuthority →
  ExpLogSubModel
complexBranchEMLModel A =
  record
    { Carrier = Complex A
    ; one = oneC A
    ; exp = expC A
    ; log = logC A
    ; sub = subC A
    }

complexBranchAdmissibility :
  (A : ComplexLogBranchAuthority) →
  EMLAdmissibility (complexBranchEMLModel A)
complexBranchAdmissibility A =
  record
    { ExpAdmissible = ExpAdmissibleC A
    ; LogAdmissible = LogAdmissibleC A
    ; SubAdmissible = SubAdmissibleC A
    }

complexBranchCompilerLaws :
  (A : ComplexLogBranchAuthority) →
  EMLCompilerLaws (complexBranchEMLModel A)
complexBranchCompilerLaws A =
  record
    { expEncoding = expEncodingLawC A
    ; logEncoding = logEncodingLawC A
    ; subEncoding = subEncodingLawC A
    }

complexBranchAnalyticPackage :
  (A : ComplexLogBranchAuthority) →
  AnalyticEMLCompilerPackage (complexBranchEMLModel A)
complexBranchAnalyticPackage A =
  record
    { laws = complexBranchCompilerLaws A
    ; admissibility = complexBranchAdmissibility A
    ; compilerDefinedness = compilerDefinednessC A
    }

------------------------------------------------------------------------
-- Explicit promotion boundary.

record ComplexBranchPromotionBoundary
  (A : ComplexLogBranchAuthority) : Set₁ where
  field
    selectedBranch : ComplexLogBranchAuthority
    selectedBranchIsA : selectedBranch ≡ A
    allInputsStayInBranch : Set
    allCompilerIntermediatesStayInBranch : Set
    principalLogSignConventionChecked : Set

open ComplexBranchPromotionBoundary public
