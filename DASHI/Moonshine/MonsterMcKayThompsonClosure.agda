module DASHI.Moonshine.MonsterMcKayThompsonClosure where

open import Agda.Primitive using (Setω)
import DASHI.Moonshine.MoonshineGroupBase as Shared

------------------------------------------------------------------------
-- This is the finite/exact modular-data endpoint needed by the first shared
-- moonshine-group theorem.  It intentionally does not assert a constructed
-- V^natural action or a complete 194-row character-table realization.

data OptionalGradedTraceRealization
  {ExactLaurentSeries : Set}
  (GradedTraceRealization : ExactLaurentSeries → Setω)
  (series : ExactLaurentSeries) : Setω where
  noGradedTraceRealization : OptionalGradedTraceRealization GradedTraceRealization series
  realizedByGradedTrace : GradedTraceRealization series →
    OptionalGradedTraceRealization GradedTraceRealization series

record MonsterMcKayThompsonClosure
  (MonsterClass FuchsianGroup ExactLaurentSeries : Set)
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set)
  (BaseCompatible :
    Shared.MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData →
    Shared.MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData → Setω)
  (ClassMoonshineGroup : MonsterClass →
    Shared.MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData)
  (ModularFor : ExactLaurentSeries →
    Shared.MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData → Set)
  (PrincipalPartIsQMinusOne CoefficientAuthority ProvenanceAudit :
    ExactLaurentSeries → Set)
  (GradedTraceRealization : ExactLaurentSeries → Setω)
  : Setω where
  field
    monsterClass : MonsterClass
    moonshineGroup : Shared.MoonshineGroupDatum MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData
    series : ExactLaurentSeries
    classGroupIdentification : BaseCompatible (ClassMoonshineGroup monsterClass)
      moonshineGroup
    modularity : ModularFor series moonshineGroup
    normalization : PrincipalPartIsQMinusOne series
    coefficientAuthority : CoefficientAuthority series
    provenanceAudit : ProvenanceAudit series
    gradedTraceRealization : OptionalGradedTraceRealization GradedTraceRealization series

open MonsterMcKayThompsonClosure public
