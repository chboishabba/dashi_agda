module DASHI.Foundations.EMLAnalyticDomain where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.ElementarySingleOperator

------------------------------------------------------------------------
-- Definedness is kept separate from total evaluation.  A concrete real or
-- complex implementation may totalize exp/log/sub internally, while this
-- predicate records exactly which source and compiled trees are analytically
-- legitimate on the selected domain and logarithm branch.

record EMLAdmissibility (M : ExpLogSubModel) : Set₁ where
  field
    ExpAdmissible : Carrier M → Set
    LogAdmissible : Carrier M → Set
    SubAdmissible : Carrier M → Carrier M → Set

open EMLAdmissibility public

data DefinedSource
  (M : ExpLogSubModel)
  (D : EMLAdmissibility M)
  (ρ : Env M) :
  ExpLogSubExpr → Set where

  oneDefined :
    DefinedSource M D ρ oneE

  varDefined :
    ∀ x →
    DefinedSource M D ρ (varE x)

  expDefined :
    ∀ {t} →
    DefinedSource M D ρ t →
    ExpAdmissible D (evalSource M ρ t) →
    DefinedSource M D ρ (expE t)

  logDefined :
    ∀ {t} →
    DefinedSource M D ρ t →
    LogAdmissible D (evalSource M ρ t) →
    DefinedSource M D ρ (logE t)

  subDefined :
    ∀ {s t} →
    DefinedSource M D ρ s →
    DefinedSource M D ρ t →
    SubAdmissible D (evalSource M ρ s) (evalSource M ρ t) →
    DefinedSource M D ρ (subE s t)

data DefinedEML
  (M : ExpLogSubModel)
  (D : EMLAdmissibility M)
  (ρ : Env M) :
  EMLExpr → Set where

  oneMDefined :
    DefinedEML M D ρ oneM

  varMDefined :
    ∀ x →
    DefinedEML M D ρ (varM x)

  emlMDefined :
    ∀ {s t} →
    DefinedEML M D ρ s →
    DefinedEML M D ρ t →
    ExpAdmissible D (evalEML M ρ s) →
    LogAdmissible D (evalEML M ρ t) →
    SubAdmissible D
      (exp M (evalEML M ρ s))
      (log M (evalEML M ρ t)) →
    DefinedEML M D ρ (emlM s t)

------------------------------------------------------------------------
-- The compiler introduces auxiliary exp/log/sub nodes.  Their closure is a
-- genuine analytic obligation and therefore has its own record, rather than
-- being hidden inside the structural compiler theorem.

record EMLCompilerDefinedness
  (M : ExpLogSubModel)
  (D : EMLAdmissibility M) : Set₁ where
  field
    expEncodingDefined :
      ∀ ρ {t} →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlExp t)

    logEncodingDefined :
      ∀ ρ {t} →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlLog t)

    subEncodingDefined :
      ∀ ρ {s t} →
      DefinedEML M D ρ s →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlSub s t)

open EMLCompilerDefinedness public

compileEML-preserves-defined :
  ∀ {M : ExpLogSubModel}
    {D : EMLAdmissibility M} →
  EMLCompilerDefinedness M D →
  ∀ ρ {t} →
  DefinedSource M D ρ t →
  DefinedEML M D ρ (compileEML t)
compileEML-preserves-defined closure ρ oneDefined =
  oneMDefined
compileEML-preserves-defined closure ρ (varDefined x) =
  varMDefined x
compileEML-preserves-defined closure ρ (expDefined sourceDefined _) =
  expEncodingDefined closure ρ
    (compileEML-preserves-defined closure ρ sourceDefined)
compileEML-preserves-defined closure ρ (logDefined sourceDefined _) =
  logEncodingDefined closure ρ
    (compileEML-preserves-defined closure ρ sourceDefined)
compileEML-preserves-defined closure ρ
  (subDefined leftDefined rightDefined _) =
  subEncodingDefined closure ρ
    (compileEML-preserves-defined closure ρ leftDefined)
    (compileEML-preserves-defined closure ρ rightDefined)

record AnalyticEMLCompilerPackage (M : ExpLogSubModel) : Set₁ where
  field
    laws : EMLCompilerLaws M
    admissibility : EMLAdmissibility M
    compilerDefinedness :
      EMLCompilerDefinedness M admissibility

open AnalyticEMLCompilerPackage public

analyticCompileCorrect :
  ∀ {M : ExpLogSubModel} →
  (P : AnalyticEMLCompilerPackage M) →
  (ρ : Env M) →
  (t : ExpLogSubExpr) →
  evalEML M ρ (compileEML t) ≡ evalSource M ρ t
analyticCompileCorrect P = compileEML-correct _ (laws P)
