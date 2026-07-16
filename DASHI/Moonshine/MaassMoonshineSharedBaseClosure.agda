module DASHI.Moonshine.MaassMoonshineSharedBaseClosure where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Fin using (Fin)

import DASHI.Core.ProjectionCategory as PC
import DASHI.Core.ProjectionFibre as PF
import DASHI.Analysis.MaassFourierCarrier as MFC
import DASHI.Analysis.MaassSpectralCertification as MSC
import DASHI.Analysis.Maass.MaassAnalyticClosure as MAC
import DASHI.Moonshine.MonsterMcKayThompsonClosure as MTC
import DASHI.Moonshine.CanonicalMaassMoonshinePostulateAudit as Audit
open import DASHI.Moonshine.MoonshineGroupBase public

------------------------------------------------------------------------
-- Definitional equality remains available to callers as a fast path, but is
-- intentionally not the relation required by the shared-base theorem.

record MaassMoonshineDefinitionalSharedFibre
  (MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set)
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set)
  (maassBase : MaassForm →
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData)
  (mckayThompsonBase : McKayThompsonSeries →
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData)
  (group : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
    discrete finiteCovolume genusZero cuspData)
  : Set where
  field
    maass : MaassForm
    moonshine : McKayThompsonSeries
    maassLivesOverGroup : maassBase maass ≡ group
    moonshineLivesOverGroup : mckayThompsonBase moonshine ≡ group

-- The mathematical shared fibre is compatible presentations of one base,
-- not syntactically identical records.
record MaassMoonshineSharedFibre
  (MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set)
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set)
  (BaseCompatible :
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData →
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData → Setω)
  (maassBase : MaassForm →
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData)
  (mckayThompsonBase : McKayThompsonSeries →
    MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData)
  (canonicalGroup : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
    discrete finiteCovolume genusZero cuspData)
  : Setω where
  field
    maass : MaassForm
    moonshine : McKayThompsonSeries
    maassBaseCompatibility : BaseCompatible (maassBase maass) canonicalGroup
    moonshineBaseCompatibility : BaseCompatible (mckayThompsonBase moonshine)
      canonicalGroup

------------------------------------------------------------------------
-- ProjectionFibre records the narrower equality-based presentation.  It is
-- retained for efficient canonical encodings, while the closure below uses
-- MaassMoonshineSharedFibre and BaseCompatible.

data SharedBaseProjectionObject : Set where
  pairedObject groupObject : SharedBaseProjectionObject

SharedBaseUnderlying :
  (MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set) →
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set) → SharedBaseProjectionObject → Set
SharedBaseUnderlying MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
  actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData pairedObject =
  MaassForm × McKayThompsonSeries
SharedBaseUnderlying MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
  actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData groupObject =
  MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
    finiteCovolume genusZero cuspData

sharedBaseProjectionCategory :
  (MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set) →
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData :
    FuchsianGroup → Set) → PC.ProjectionCategory
sharedBaseProjectionCategory MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
  actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData = record
  { Obj = SharedBaseProjectionObject
  ; Hom = λ A B →
      SharedBaseUnderlying MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
        actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData A →
      SharedBaseUnderlying MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
        actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData B
  ; id = λ x → x
  ; _∘_ = λ g f x → g (f x)
  ; id-left = λ f → refl
  ; id-right = λ f → refl
  ; assoc = λ f g h → refl
  ; categoryReading = "Pi_shared-base(pair/group)"
  }

sharedBaseProjectionFibre :
  {MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set} →
  {actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData : FuchsianGroup → Set} →
  (maassBase : MaassForm → MoonshineGroupDatum MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData) →
  PF.ProjectionFibre (sharedBaseProjectionCategory MaassForm McKayThompsonSeries
    MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData)
sharedBaseProjectionFibre {MaassForm} {McKayThompsonSeries} {MonsterClass}
  {FuchsianGroup} {actsOnUpperHalfPlane} {discrete} {finiteCovolume} {genusZero}
  {cuspData} maassBase = record
  { Underlying = SharedBaseUnderlying MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData
  ; Carrier = pairedObject
  ; Observable = groupObject
  ; π = λ pair → maassBase (Data.Product.proj₁ pair)
  ; apply = λ f x → f x
  ; fibreReading = "Definitional shared moonshine-group fibre"
  }

toMaassProjectionFibre :
  {MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set} →
  {actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData : FuchsianGroup → Set} →
  {maassBase : MaassForm → MoonshineGroupDatum MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData} →
  {mckayThompsonBase : McKayThompsonSeries → MoonshineGroupDatum MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData} →
  {group : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
    discrete finiteCovolume genusZero cuspData} →
  MaassMoonshineDefinitionalSharedFibre MaassForm McKayThompsonSeries MonsterClass
    FuchsianGroup actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData
    maassBase mckayThompsonBase group →
  PF.ProjectionFibre.Fibre (sharedBaseProjectionFibre maassBase) group
toMaassProjectionFibre shared =
  (MaassMoonshineDefinitionalSharedFibre.maass shared ,
    MaassMoonshineDefinitionalSharedFibre.moonshine shared) ,
  MaassMoonshineDefinitionalSharedFibre.maassLivesOverGroup shared

record SharedFibreRefinementPersistence
  {MaassForm McKayThompsonSeries MonsterClass FuchsianGroup : Set}
  {actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData : FuchsianGroup → Set}
  {BaseCompatible : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData → MoonshineGroupDatum MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData → Setω}
  {maassBase : MaassForm → MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData}
  {mckayThompsonBase : McKayThompsonSeries → MoonshineGroupDatum MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData}
  {canonicalGroup : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData}
  (shared : MaassMoonshineSharedFibre MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData BaseCompatible maassBase
    mckayThompsonBase canonicalGroup)
  (MaassRefinement MoonshinePresentationChange : Set)
  (refineMaass : MaassRefinement → MaassForm → MaassForm)
  (transportMoonshine : MoonshinePresentationChange → McKayThompsonSeries → McKayThompsonSeries)
  : Setω where
  field
    maassBasePreserved : ∀ refinement → BaseCompatible
      (maassBase (refineMaass refinement (MaassMoonshineSharedFibre.maass shared))) canonicalGroup
    moonshineBasePreserved : ∀ change → BaseCompatible
      (mckayThompsonBase (transportMoonshine change (MaassMoonshineSharedFibre.moonshine shared)))
      canonicalGroup

record MaassMoonshineSharedBaseClosure
  (Γ : MFC.ΓMaass)
  (Bytes Digest Payload MaassForm SpectralInterval Radius Cusp SpectralParameter
    ConstantTerm McKayThompsonSeries MonsterClass FuchsianGroup
    MaassRefinement MoonshinePresentationChange : Set)
  (eigenvalueIn : MaassForm → SpectralInterval → Set)
  (candidateWithin : MSC.CandidateMaassForm Γ → MaassForm → Radius → Set)
  (EisensteinFamily : Cusp → SpectralParameter → Set)
  (constantTerm : MSC.CandidateMaassForm Γ → Cusp → ConstantTerm)
  (constantTermIsZero : ConstantTerm → Set)
  (continuousProjectionSmall : MSC.CandidateMaassForm Γ → Set)
  (windowAvoidsResidualSpectrum : SpectralInterval → Set)
  (windowSeparatedFromContinuousSpectrum : SpectralInterval → Set)
  (actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData : FuchsianGroup → Set)
  (BaseCompatible : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData → MoonshineGroupDatum MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData → Setω)
  (ClassMoonshineGroup : MonsterClass → MoonshineGroupDatum MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData)
  (ModularFor : McKayThompsonSeries → MoonshineGroupDatum MonsterClass FuchsianGroup
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData → Set)
  (PrincipalPartIsQMinusOne CoefficientAuthority ProvenanceAudit :
    McKayThompsonSeries → Set)
  (GradedTraceRealization : McKayThompsonSeries → Setω)
  (maassBase : MaassForm → MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane
      discrete finiteCovolume genusZero cuspData)
  (mckayThompsonBase : McKayThompsonSeries → MoonshineGroupDatum MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData)
  (refineMaass : MaassRefinement → MaassForm → MaassForm)
  (transportMoonshine : MoonshinePresentationChange → McKayThompsonSeries → McKayThompsonSeries)
  : Setω where
  field
    maassClosure : MAC.MaassAnalyticClosure Γ Bytes Digest Payload MaassForm SpectralInterval Radius
      Cusp SpectralParameter ConstantTerm eigenvalueIn candidateWithin EisensteinFamily constantTerm
      constantTermIsZero continuousProjectionSmall windowAvoidsResidualSpectrum
      windowSeparatedFromContinuousSpectrum
    monsterClosure : MTC.MonsterMcKayThompsonClosure MonsterClass FuchsianGroup
      McKayThompsonSeries actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData
      BaseCompatible ClassMoonshineGroup ModularFor PrincipalPartIsQMinusOne
      CoefficientAuthority ProvenanceAudit GradedTraceRealization
    canonicalGroup : MoonshineGroupDatum MonsterClass FuchsianGroup actsOnUpperHalfPlane discrete
      finiteCovolume genusZero cuspData
    sharedFibre : MaassMoonshineSharedFibre MaassForm McKayThompsonSeries MonsterClass FuchsianGroup
      actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData BaseCompatible maassBase
      mckayThompsonBase canonicalGroup
    sharedFibreUsesCertifiedMaass : MaassMoonshineSharedFibre.maass sharedFibre ≡
      MAC.certifiedForm maassClosure
    sharedFibreUsesCertifiedSeries : MaassMoonshineSharedFibre.moonshine sharedFibre ≡
      MTC.series monsterClosure
    refinementPersistence : SharedFibreRefinementPersistence sharedFibre MaassRefinement
      MoonshinePresentationChange refineMaass transportMoonshine
    sourceAuthorityAudit : Audit.MaassMoonshineFieldAudit
    noUntrackedEssentialAssumptions : Audit.NoUntrackedEssentialAssumptions sourceAuthorityAudit

data SharedMoonshineGroupPromotion
  {Γ Bytes Digest Payload MaassForm SpectralInterval Radius Cusp SpectralParameter ConstantTerm
    McKayThompsonSeries MonsterClass FuchsianGroup MaassRefinement
    MoonshinePresentationChange eigenvalueIn candidateWithin EisensteinFamily constantTerm
    constantTermIsZero continuousProjectionSmall windowAvoidsResidualSpectrum
    windowSeparatedFromContinuousSpectrum actsOnUpperHalfPlane discrete finiteCovolume genusZero
    cuspData BaseCompatible ClassMoonshineGroup ModularFor PrincipalPartIsQMinusOne
    CoefficientAuthority ProvenanceAudit GradedTraceRealization maassBase mckayThompsonBase
    refineMaass transportMoonshine} : Setω where
  promoteSharedBase : MaassMoonshineSharedBaseClosure Γ Bytes Digest Payload MaassForm
    SpectralInterval Radius Cusp SpectralParameter ConstantTerm McKayThompsonSeries MonsterClass
    FuchsianGroup MaassRefinement MoonshinePresentationChange
    eigenvalueIn candidateWithin EisensteinFamily constantTerm constantTermIsZero
    continuousProjectionSmall windowAvoidsResidualSpectrum windowSeparatedFromContinuousSpectrum
    actsOnUpperHalfPlane discrete finiteCovolume genusZero cuspData BaseCompatible
    ClassMoonshineGroup ModularFor PrincipalPartIsQMinusOne CoefficientAuthority ProvenanceAudit
    GradedTraceRealization maassBase mckayThompsonBase refineMaass transportMoonshine →
    SharedMoonshineGroupPromotion
