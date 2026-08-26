{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.ReusableTemplateTrancheEconomyExact where

open import Agda.Builtin.Equality using (_≡_)

record ReusableCompiledTemplate
  (Input Template Authority Work : Set)
  (LeqWork : Work → Work → Set)
  : Set₁ where
  field
    buildTemplate : Input → Template
    coldCompile : Input → Authority
    reuseCompile : Template → Input → Authority
    reuseAuthorityExact :
      (source target : Input) →
      reuseCompile (buildTemplate source) target ≡ coldCompile target
    coldWork : Input → Work
    reuseWork : Template → Input → Work
    reuseWorkNotIncreased :
      (source target : Input) →
      LeqWork (reuseWork (buildTemplate source) target) (coldWork target)

open ReusableCompiledTemplate public

record TemplateAdmissibility (Input Template : Set) : Set₁ where
  field
    Admissible : Template → Input → Set

open TemplateAdmissibility public

record AdmissibleTemplateReuse
  {Input Template : Set}
  (admissibility : TemplateAdmissibility Input Template)
  (template : Template)
  (target : Input)
  : Set where
  field
    witness : Admissible admissibility template target

open AdmissibleTemplateReuse public

reusePreservesAuthority :
  ∀ {Input Template Authority Work : Set}
    {LeqWork : Work → Work → Set}
    (system : ReusableCompiledTemplate Input Template Authority Work LeqWork)
    (source target : Input) →
  reuseCompile system (buildTemplate system source) target
    ≡ coldCompile system target
reusePreservesAuthority system = reuseAuthorityExact system

reuseCarriesDeclaredWorkBound :
  ∀ {Input Template Authority Work : Set}
    {LeqWork : Work → Work → Set}
    (system : ReusableCompiledTemplate Input Template Authority Work LeqWork)
    (source target : Input) →
  LeqWork
    (reuseWork system (buildTemplate system source) target)
    (coldWork system target)
reuseCarriesDeclaredWorkBound system = reuseWorkNotIncreased system
