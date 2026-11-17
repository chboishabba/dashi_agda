{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFamilyRound529Exact where

------------------------------------------------------------------------
-- GOAL-1 C0 / ROUND529:
-- CONCRETE LOCAL GAUGE-INVARIANT OBSERVABLE FAMILY FROM WILSON PLAQUETTES
--
-- CompactLieLatticeGauge already proves that every closed-loop class-function
-- observable is gauge invariant.  The missing locality half is elementary:
-- holonomy along a path depends only on the edge values on that path.
--
-- Therefore, once the literal configuration carrier is decoded as a gauge
-- field and one closed local Wilson path/class function is selected per
-- position, the required observable family is compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.CompactLieGroupCore

import DASHI.Physics.YangMills.CompactLieLatticeGauge as Lattice

data AgreesOnPath
    {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    (left right : Lattice.GaugeField {G = GroupElement} Edge)
    : ∀ {start finish} → Lattice.Path Edge start finish → Set where
  emptyAgreement :
    ∀ {point} →
    AgreesOnPath left right (Lattice.empty {x = point})

  stepAgreement :
    ∀ {start middle finish}
      {edge : Edge start middle}
      {rest : Lattice.Path Edge middle finish} →
    left start middle edge ≡ right start middle edge →
    AgreesOnPath left right rest →
    AgreesOnPath left right (edge Lattice.▷ rest)

holonomyDependsOnlyOnPath :
  ∀ {Vertex GroupElement : Set}
    {Edge : Vertex → Vertex → Set}
    {start finish}
    (H : Group GroupElement)
    (left right : Lattice.GaugeField {G = GroupElement} Edge)
    (path : Lattice.Path Edge start finish) →
  AgreesOnPath left right path →
  Lattice.holonomy H left path
  ≡ Lattice.holonomy H right path
holonomyDependsOnlyOnPath H left right Lattice.empty emptyAgreement = refl
holonomyDependsOnlyOnPath H left right
    (edge Lattice.▷ rest)
    (stepAgreement edgeSame restSame)
  rewrite edgeSame
        | holonomyDependsOnlyOnPath H left right rest restSame
  = refl

record WilsonLocalObservableAt
    (Configuration Position Vertex GroupElement : Set)
    (Edge : Vertex → Vertex → Set)
    (H : Group GroupElement) : Set₁ where
  field
    decode :
      Configuration →
      Lattice.GaugeField {G = GroupElement} Edge

    baseAt : Position → Vertex

    boundaryAt :
      ∀ position →
      Lattice.Path Edge (baseAt position) (baseAt position)

    classValue : GroupElement → ℝ
    classFunction : Lattice.ClassFunction H classValue

open WilsonLocalObservableAt public

wilsonObservable :
  ∀ {Configuration Position Vertex GroupElement Edge H} →
  WilsonLocalObservableAt
    Configuration Position Vertex GroupElement Edge H →
  Position → Configuration → ℝ
wilsonObservable {H = H} source position configuration =
  Lattice.loopObservable H
    (classValue source)
    (decode source configuration)
    (boundaryAt source position)

wilsonObservableGaugeInvariant :
  ∀ {Configuration Position Vertex GroupElement Edge H}
    (source :
      WilsonLocalObservableAt
        Configuration Position Vertex GroupElement Edge H)
    position configuration gamma →
  Lattice.loopObservable H
    (classValue source)
    (Lattice.gaugeAction H gamma (decode source configuration))
    (boundaryAt source position)
  ≡
  wilsonObservable source position configuration
wilsonObservableGaugeInvariant {H = H} source position configuration gamma =
  Lattice.loopObservableGaugeInvariant H
    (classValue source)
    (classFunction source)
    gamma
    (decode source configuration)
    (boundaryAt source position)

wilsonObservableLocal :
  ∀ {Configuration Position Vertex GroupElement Edge H}
    (source :
      WilsonLocalObservableAt
        Configuration Position Vertex GroupElement Edge H)
    position left right →
  AgreesOnPath
    (decode source left)
    (decode source right)
    (boundaryAt source position) →
  wilsonObservable source position left
  ≡ wilsonObservable source position right
wilsonObservableLocal {H = H} source position left right agreement =
  cong (classValue source)
    (holonomyDependsOnlyOnPath H
      (decode source left)
      (decode source right)
      (boundaryAt source position)
      agreement)

------------------------------------------------------------------------
-- All-group family.  Group/vertex/edge carriers may depend on the selected G;
-- the literal Observable carrier remains Configuration -> R.
------------------------------------------------------------------------

record WilsonLocalObservableFamily
    (GaugeIndex Configuration Position : Set) : Set₂ where
  field
    Vertex : GaugeIndex → Set
    GroupElement : GaugeIndex → Set
    Edge :
      ∀ group →
      Vertex group → Vertex group → Set

    groupStructure :
      ∀ group → Group (GroupElement group)

    source :
      ∀ group →
      WilsonLocalObservableAt
        Configuration Position
        (Vertex group)
        (GroupElement group)
        (Edge group)
        (groupStructure group)

open WilsonLocalObservableFamily public

localObservable :
  ∀ {GaugeIndex Configuration Position} →
  WilsonLocalObservableFamily GaugeIndex Configuration Position →
  GaugeIndex → Position → Configuration → ℝ
localObservable family group =
  wilsonObservable (source family group)

round529PathLocalityCompilerLevel : ProofLevel
round529PathLocalityCompilerLevel = machineChecked

round529WilsonGaugeInvarianceCompilerLevel : ProofLevel
round529WilsonGaugeInvarianceCompilerLevel = machineChecked

round529LocalObservableFamilyCompilerLevel : ProofLevel
round529LocalObservableFamilyCompilerLevel = machineChecked

-- Physical realization still required: decode the literal configuration as the
-- actual gauge field and select the local closed Wilson path/class function for
-- every group and position.
literalRound529WilsonLocalObservableRealizationLevel : ProofLevel
literalRound529WilsonLocalObservableRealizationLevel = conditional
