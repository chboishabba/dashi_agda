module DASHI.Reasoning.TrialecticWavePhasePseudofunctorCoherenceExact where

------------------------------------------------------------------------
-- FULL-SITE PSEUDOFUNCTOR COHERENCE + C3 EQUIVARIANCE
--
-- The Set-valued presheaf already proves restriction identity/composition.
-- The wave-phase groupoid presheaf turns those equalities into zero-phase
-- isomorphisms, i.e. the unitors/compositors of a contravariant groupoid-valued
-- pseudofunctor.  Since every structural 2-cell has phase zero, the coherence
-- diagrams commute in the phase setoid exactly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as SetEffective
import DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact as Phase

------------------------------------------------------------------------
-- 1. Unit and composition comparison isomorphisms.
------------------------------------------------------------------------

unitIso :
  ∀ {U : Site.RelObj}
    (x : Presheaf.Section U) →
  Phase.FibreHom
    (Presheaf.restrict (Site.idR U) x)
    x
unitIso x = Phase.identityHom x

zeroPhaseFromEquality :
  ∀ {U : Site.RelObj}
    {left right : Presheaf.Section U} →
  left ≡ right →
  Phase.FibreHom left right
zeroPhaseFromEquality {Site.globalABC} eq =
  Phase.global-phase-hom
    (SetEffective.boundary-observational-equivalence
      (cong Cell.edgeAB eq)
      (cong Cell.edgeBC eq)
      (cong Cell.edgeCA eq))
    Tri.triZero
zeroPhaseFromEquality {Site.edgeAB} eq = Phase.phase-equality-hom eq Tri.triZero
zeroPhaseFromEquality {Site.edgeBC} eq = Phase.phase-equality-hom eq Tri.triZero
zeroPhaseFromEquality {Site.edgeCA} eq = Phase.phase-equality-hom eq Tri.triZero
zeroPhaseFromEquality {Site.vertexA} eq = Phase.phase-equality-hom eq Tri.triZero
zeroPhaseFromEquality {Site.vertexB} eq = Phase.phase-equality-hom eq Tri.triZero
zeroPhaseFromEquality {Site.vertexC} eq = Phase.phase-equality-hom eq Tri.triZero

compositorIso :
  ∀ {U V W : Site.RelObj}
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    (x : Presheaf.Section W) →
  Phase.FibreHom
    (Presheaf.restrict (Site.composeRel g f) x)
    (Presheaf.restrict f (Presheaf.restrict g x))
compositorIso g f x =
  zeroPhaseFromEquality (Presheaf.restrictComposition g f x)

------------------------------------------------------------------------
-- 2. Coherence is phase-trivial: every structural comparison has zero phase.
------------------------------------------------------------------------

unitIsoHasZeroPhase :
  ∀ {U : Site.RelObj}
    (x : Presheaf.Section U) →
  Phase.phaseOf (unitIso x) ≡ Tri.triZero
unitIsoHasZeroPhase x = refl

compositorHasZeroPhase :
  ∀ {U V W : Site.RelObj}
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    (x : Presheaf.Section W) →
  Phase.phaseOf (compositorIso g f x) ≡ Tri.triZero
compositorHasZeroPhase g f x = refl

pseudofunctorPentagonPhaseCoherence :
  ∀ {U V W X : Site.RelObj}
    (h : Site.RelHom W X)
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    (x : Presheaf.Section X) →
  Tri.triAdd
    (Phase.phaseOf (compositorIso h g x))
    (Phase.phaseOf
      (compositorIso (Site.composeRel h g) f x))
  ≡
  Tri.triAdd
    (Phase.phaseOf
      (compositorIso g f (Presheaf.restrict h x)))
    (Phase.phaseOf (compositorIso h (Site.composeRel g f) x))
pseudofunctorPentagonPhaseCoherence h g f x = refl

pseudofunctorLeftUnitPhaseCoherence :
  ∀ {U V : Site.RelObj}
    (f : Site.RelHom U V)
    (x : Presheaf.Section V) →
  Tri.triAdd
    (Phase.phaseOf (unitIso (Presheaf.restrict f x)))
    (Phase.phaseOf (compositorIso (Site.idR V) f x))
  ≡ Tri.triZero
pseudofunctorLeftUnitPhaseCoherence f x = refl

pseudofunctorRightUnitPhaseCoherence :
  ∀ {U V : Site.RelObj}
    (f : Site.RelHom U V)
    (x : Presheaf.Section V) →
  Tri.triAdd
    (Phase.phaseOf (compositorIso f (Site.idR U) x))
    (Phase.phaseOf (unitIso x))
  ≡ Tri.triZero
pseudofunctorRightUnitPhaseCoherence f x = refl

------------------------------------------------------------------------
-- 3. Site-wide C3 equivariance as a phase action, separate from restriction.
------------------------------------------------------------------------

c3Generator :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  Phase.FibreHom x x
c3Generator = Phase.positivePhaseAutomorphism

c3GeneratorTwice :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  Phase.FibreHom x x
c3GeneratorTwice x = Phase.composeHom (c3Generator x) (c3Generator x)

c3GeneratorThrice :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  Phase.FibreHom x x
c3GeneratorThrice x = Phase.composeHom (c3Generator x) (c3GeneratorTwice x)

c3GeneratorCubedIsIdentity :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  c3GeneratorThrice x Phase.≈ₚ Phase.identityHom x
c3GeneratorCubedIsIdentity x = refl

c3GeneratorCommutesWithRestriction :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    (x : Presheaf.Section V) →
  Phase.restrictHom arrow (c3Generator x)
  Phase.≈ₚ
  c3Generator (Presheaf.restrict arrow x)
c3GeneratorCommutesWithRestriction arrow x = refl

record TrialecticWavePhasePseudofunctorBoundary : Set where
  constructor trialectic-wave-phase-pseudofunctor-boundary
  field
    unitComparisonsConstructed : Bool
    compositionComparisonsConstructed : Bool
    pentagonPhaseCoherencePaid : Bool
    leftRightUnitPhaseCoherencePaid : Bool
    siteWideC3GeneratorConstructed : Bool
    c3GeneratorCubedIsIdentityPaid : Bool
    c3EquivarianceCommutesWithEveryRestriction : Bool
    c3ChartRotationIdentifiedWithRestriction : Bool
    fullSiteTransportPseudofunctorPaid : Bool

open TrialecticWavePhasePseudofunctorBoundary public

canonicalTrialecticWavePhasePseudofunctorBoundary :
  TrialecticWavePhasePseudofunctorBoundary
canonicalTrialecticWavePhasePseudofunctorBoundary =
  trialectic-wave-phase-pseudofunctor-boundary
    true true true true true true true false true
