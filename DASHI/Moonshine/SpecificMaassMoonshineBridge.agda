module DASHI.Moonshine.SpecificMaassMoonshineBridge where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- A restricted construction, never a generic Maaß-to-Monster arrow.
-- Hecke/replication operations are parameters because the appropriate
-- operation depends on the named construction and normalisation.

record NamedMoonshineConstruction : Set where
  field
    constructionName : String
    constructionReference : String

record SpecificMaassMoonshineBridge
  (MaassForm McKayThompsonSeries Prime : Set)
  (ConstructionDomain : MaassForm → Set)
  (maassHecke : Prime → MaassForm → MaassForm)
  (moonshineHecke : Prime → McKayThompsonSeries → McKayThompsonSeries)
  (coefficientTraceLaw : McKayThompsonSeries → Set)
  (f : MaassForm) (Tg : McKayThompsonSeries) : Setω where
  field
    construction : NamedMoonshineConstruction
    domainCondition : ConstructionDomain f
    lift : ∀ {source} → ConstructionDomain source → McKayThompsonSeries
    targetIsTg : lift domainCondition ≡ Tg
    heckePreservesDomain :
      ∀ p → ConstructionDomain (maassHecke p f)
    heckeIntertwining :
      ∀ p → lift (heckePreservesDomain p) ≡ moonshineHecke p Tg
    traceCoefficients : coefficientTraceLaw Tg

GenericMaassToMonsterArrow : Set → Set → Set
GenericMaassToMonsterArrow MaassForm MonsterRepresentation = MaassForm → MonsterRepresentation
