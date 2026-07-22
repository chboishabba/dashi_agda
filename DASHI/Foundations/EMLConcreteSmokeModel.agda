module DASHI.Foundations.EMLConcreteSmokeModel where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.ElementarySingleOperator
open import DASHI.Foundations.EMLAnalyticDomain

------------------------------------------------------------------------
-- A fully concrete, deliberately degenerate model used only to exercise the
-- compiler and definedness plumbing in CI.  It is not the real or complex
-- analytic authority and cannot promote scientific-calculator semantics.

data Singleton : Set where
  singleton : Singleton

data Top : Set where
  top : Top

smokeModel : ExpLogSubModel
smokeModel =
  record
    { Carrier = Singleton
    ; one = singleton
    ; exp = λ _ → singleton
    ; log = λ _ → singleton
    ; sub = λ _ _ → singleton
    }

smokeLaws : EMLCompilerLaws smokeModel
smokeLaws =
  record
    { expEncoding = λ _ → refl
    ; logEncoding = λ _ → refl
    ; subEncoding = λ _ _ → refl
    }

smokeAdmissibility : EMLAdmissibility smokeModel
smokeAdmissibility =
  record
    { ExpAdmissible = λ _ → Top
    ; LogAdmissible = λ _ → Top
    ; SubAdmissible = λ _ _ → Top
    }

allEMLDefined :
  ∀ ρ t →
  DefinedEML smokeModel smokeAdmissibility ρ t
allEMLDefined ρ oneM = oneMDefined
allEMLDefined ρ (varM x) = varMDefined x
allEMLDefined ρ (emlM s t) =
  emlMDefined
    (allEMLDefined ρ s)
    (allEMLDefined ρ t)
    top
    top
    top

smokeDefinedness :
  EMLCompilerDefinedness smokeModel smokeAdmissibility
smokeDefinedness =
  record
    { expEncodingDefined = λ ρ {t} _ → allEMLDefined ρ (emlExp t)
    ; logEncodingDefined = λ ρ {t} _ → allEMLDefined ρ (emlLog t)
    ; subEncodingDefined = λ ρ {s} {t} _ _ → allEMLDefined ρ (emlSub s t)
    }

smokeAnalyticPackage : AnalyticEMLCompilerPackage smokeModel
smokeAnalyticPackage =
  record
    { laws = smokeLaws
    ; admissibility = smokeAdmissibility
    ; compilerDefinedness = smokeDefinedness
    }

smokeCompileCorrect :
  ∀ ρ t →
  evalEML smokeModel ρ (compileEML t)
  ≡ evalSource smokeModel ρ t
smokeCompileCorrect = compileEML-correct smokeModel smokeLaws
