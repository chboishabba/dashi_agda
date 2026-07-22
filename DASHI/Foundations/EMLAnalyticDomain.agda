module DASHI.Foundations.EMLAnalyticDomain where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.ElementarySingleOperator

------------------------------------------------------------------------
-- Definedness is kept separate from total evaluation.  A concrete real or
-- complex implementation may totalize exp/log/sub internally, while these
-- predicates record exactly which source and compiled trees are analytically
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
-- A globally closed model can expose one reusable closure theorem.  This is a
-- convenience for smoke/total models, not a requirement for branch-sensitive
-- real or complex models.

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

------------------------------------------------------------------------
-- Branch-safe compilation is expression-indexed.  This avoids the false
-- requirement that every carrier value be a legal logarithm input.  Each
-- constructor carries source definedness recursively and the proof that the
-- exact compiled node, including all introduced intermediates, is defined.

data CompilationDefined
  (M : ExpLogSubModel)
  (D : EMLAdmissibility M)
  (ρ : Env M) :
  ExpLogSubExpr → Set where

  oneCompilationDefined :
    CompilationDefined M D ρ oneE

  varCompilationDefined :
    ∀ x →
    CompilationDefined M D ρ (varE x)

  expCompilationDefined :
    ∀ {t} →
    CompilationDefined M D ρ t →
    ExpAdmissible D (evalSource M ρ t) →
    DefinedEML M D ρ (emlExp (compileEML t)) →
    CompilationDefined M D ρ (expE t)

  logCompilationDefined :
    ∀ {t} →
    CompilationDefined M D ρ t →
    LogAdmissible D (evalSource M ρ t) →
    DefinedEML M D ρ (emlLog (compileEML t)) →
    CompilationDefined M D ρ (logE t)

  subCompilationDefined :
    ∀ {s t} →
    CompilationDefined M D ρ s →
    CompilationDefined M D ρ t →
    SubAdmissible D (evalSource M ρ s) (evalSource M ρ t) →
    DefinedEML M D ρ (emlSub (compileEML s) (compileEML t)) →
    CompilationDefined M D ρ (subE s t)

sourceDefinedFromCompilation :
  ∀ {M : ExpLogSubModel}
    {D : EMLAdmissibility M}
    {ρ : Env M}
    {t : ExpLogSubExpr} →
  CompilationDefined M D ρ t →
  DefinedSource M D ρ t
sourceDefinedFromCompilation oneCompilationDefined = oneDefined
sourceDefinedFromCompilation (varCompilationDefined x) = varDefined x
sourceDefinedFromCompilation
  (expCompilationDefined child admissible compiled) =
  expDefined (sourceDefinedFromCompilation child) admissible
sourceDefinedFromCompilation
  (logCompilationDefined child admissible compiled) =
  logDefined (sourceDefinedFromCompilation child) admissible
sourceDefinedFromCompilation
  (subCompilationDefined left right admissible compiled) =
  subDefined
    (sourceDefinedFromCompilation left)
    (sourceDefinedFromCompilation right)
    admissible

compiledDefinedFromCompilation :
  ∀ {M : ExpLogSubModel}
    {D : EMLAdmissibility M}
    {ρ : Env M}
    {t : ExpLogSubExpr} →
  CompilationDefined M D ρ t →
  DefinedEML M D ρ (compileEML t)
compiledDefinedFromCompilation oneCompilationDefined = oneMDefined
compiledDefinedFromCompilation (varCompilationDefined x) = varMDefined x
compiledDefinedFromCompilation
  (expCompilationDefined child admissible compiled) = compiled
compiledDefinedFromCompilation
  (logCompilationDefined child admissible compiled) = compiled
compiledDefinedFromCompilation
  (subCompilationDefined left right admissible compiled) = compiled

globalClosureBuildsCompilation :
  ∀ {M : ExpLogSubModel}
    {D : EMLAdmissibility M} →
  EMLCompilerDefinedness M D →
  ∀ ρ {t} →
  DefinedSource M D ρ t →
  CompilationDefined M D ρ t
globalClosureBuildsCompilation closure ρ oneDefined =
  oneCompilationDefined
globalClosureBuildsCompilation closure ρ (varDefined x) =
  varCompilationDefined x
globalClosureBuildsCompilation closure ρ
  (expDefined sourceDefined admissible) =
  expCompilationDefined
    childCompilation
    admissible
    (expEncodingDefined closure ρ
      (compiledDefinedFromCompilation childCompilation))
  where
    childCompilation =
      globalClosureBuildsCompilation closure ρ sourceDefined
globalClosureBuildsCompilation closure ρ
  (logDefined sourceDefined admissible) =
  logCompilationDefined
    childCompilation
    admissible
    (logEncodingDefined closure ρ
      (compiledDefinedFromCompilation childCompilation))
  where
    childCompilation =
      globalClosureBuildsCompilation closure ρ sourceDefined
globalClosureBuildsCompilation closure ρ
  (subDefined leftDefined rightDefined admissible) =
  subCompilationDefined
    leftCompilation
    rightCompilation
    admissible
    (subEncodingDefined closure ρ
      (compiledDefinedFromCompilation leftCompilation)
      (compiledDefinedFromCompilation rightCompilation))
  where
    leftCompilation =
      globalClosureBuildsCompilation closure ρ leftDefined
    rightCompilation =
      globalClosureBuildsCompilation closure ρ rightDefined

------------------------------------------------------------------------
-- Branch/domain-sensitive semantic laws are required only when the exact
-- encoded node and its children are all certified as defined.

record EMLCompilerLawsOnDomain
  (M : ExpLogSubModel)
  (D : EMLAdmissibility M) : Set₁ where
  field
    expEncodingOnDomain :
      ∀ ρ {t} →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlExp t) →
      evalEML M ρ (emlExp t)
      ≡ exp M (evalEML M ρ t)

    logEncodingOnDomain :
      ∀ ρ {t} →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlLog t) →
      evalEML M ρ (emlLog t)
      ≡ log M (evalEML M ρ t)

    subEncodingOnDomain :
      ∀ ρ {s t} →
      DefinedEML M D ρ s →
      DefinedEML M D ρ t →
      DefinedEML M D ρ (emlSub s t) →
      evalEML M ρ (emlSub s t)
      ≡ sub M (evalEML M ρ s) (evalEML M ρ t)

open EMLCompilerLawsOnDomain public

globalLawsGiveDomainLaws :
  ∀ {M : ExpLogSubModel} {D : EMLAdmissibility M} →
  EMLCompilerLaws M →
  EMLCompilerLawsOnDomain M D
globalLawsGiveDomainLaws laws =
  record
    { expEncodingOnDomain =
        λ ρ {t} childDefined compiledDefined →
          expEncoding laws (evalEML _ ρ t)
    ; logEncodingOnDomain =
        λ ρ {t} childDefined compiledDefined →
          logEncoding laws (evalEML _ ρ t)
    ; subEncodingOnDomain =
        λ ρ {s} {t} leftDefined rightDefined compiledDefined →
          subEncoding laws (evalEML _ ρ s) (evalEML _ ρ t)
    }

record AnalyticEMLCompilerPackage (M : ExpLogSubModel) : Set₁ where
  field
    admissibility : EMLAdmissibility M
    compilerLawsOnDomain :
      EMLCompilerLawsOnDomain M admissibility

open AnalyticEMLCompilerPackage public

analyticCompileCorrect :
  ∀ {M : ExpLogSubModel} →
  (P : AnalyticEMLCompilerPackage M) →
  ∀ ρ {t} →
  CompilationDefined M (admissibility P) ρ t →
  evalEML M ρ (compileEML t) ≡ evalSource M ρ t
analyticCompileCorrect P ρ oneCompilationDefined = refl
analyticCompileCorrect P ρ (varCompilationDefined x) = refl
analyticCompileCorrect P ρ
  (expCompilationDefined child admissible compiled)
  rewrite analyticCompileCorrect P ρ child =
  expEncodingOnDomain
    (compilerLawsOnDomain P)
    ρ
    (compiledDefinedFromCompilation child)
    compiled
analyticCompileCorrect P ρ
  (logCompilationDefined child admissible compiled)
  rewrite analyticCompileCorrect P ρ child =
  logEncodingOnDomain
    (compilerLawsOnDomain P)
    ρ
    (compiledDefinedFromCompilation child)
    compiled
analyticCompileCorrect P ρ
  (subCompilationDefined left right admissible compiled)
  rewrite analyticCompileCorrect P ρ left
        | analyticCompileCorrect P ρ right =
  subEncodingOnDomain
    (compilerLawsOnDomain P)
    ρ
    (compiledDefinedFromCompilation left)
    (compiledDefinedFromCompilation right)
    compiled
