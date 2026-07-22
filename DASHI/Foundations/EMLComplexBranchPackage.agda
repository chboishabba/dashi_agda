module DASHI.Foundations.EMLComplexBranchPackage where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- A logarithm branch is data, not an ambient global convention.  Complex exp
-- and subtraction are treated as total; logarithm definedness is exactly the
-- selected branch domain.  Both semantic identities and compiler closure are
-- required only on the certified branch, not globally across a branch cut.

data ComplexAlways : Set where
  complexAlways : ComplexAlways

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

    compilerDefinednessC :
      let M = record
            { Carrier = Complex
            ; one = oneC
            ; exp = expC
            ; log = logC
            ; sub = subC
            }
          D = record
            { ExpAdmissible = λ _ → ComplexAlways
            ; LogAdmissible = BranchDomain
            ; SubAdmissible = λ _ _ → ComplexAlways
            }
      in EMLCompilerDefinedness M D

    compilerLawsOnDomainC :
      let M = record
            { Carrier = Complex
            ; one = oneC
            ; exp = expC
            ; log = logC
            ; sub = subC
            }
          D = record
            { ExpAdmissible = λ _ → ComplexAlways
            ; LogAdmissible = BranchDomain
            ; SubAdmissible = λ _ _ → ComplexAlways
            }
      in EMLCompilerLawsOnDomain M D

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
    { ExpAdmissible = λ _ → ComplexAlways
    ; LogAdmissible = BranchDomain A
    ; SubAdmissible = λ _ _ → ComplexAlways
    }

complexBranchAnalyticPackage :
  (A : ComplexLogBranchAuthority) →
  AnalyticEMLCompilerPackage (complexBranchEMLModel A)
complexBranchAnalyticPackage A =
  record
    { admissibility = complexBranchAdmissibility A
    ; compilerDefinedness = compilerDefinednessC A
    ; compilerLawsOnDomain = compilerLawsOnDomainC A
    }

------------------------------------------------------------------------
-- Explicit promotion boundary.

record ComplexBranchPromotionBoundary
  (A : ComplexLogBranchAuthority) : Set₁ where
  field
    AdmissibleInput : Complex A → Set
    CompilerIntermediate : Complex A → Set

    admissibleInputInBranch :
      ∀ z →
      AdmissibleInput z →
      BranchDomain A z

    compilerIntermediateInBranch :
      ∀ z →
      CompilerIntermediate z →
      BranchDomain A z

    derivedImaginaryUnit : Complex A
    standardImaginaryUnit : Complex A
    principalLogSignConventionChecked :
      derivedImaginaryUnit ≡ standardImaginaryUnit

open ComplexBranchPromotionBoundary public
