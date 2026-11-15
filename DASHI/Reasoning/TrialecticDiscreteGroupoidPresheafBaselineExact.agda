module DASHI.Reasoning.TrialecticDiscreteGroupoidPresheafBaselineExact where

------------------------------------------------------------------------
-- FULL-SITE DISCRETE GROUPOID PRESHEAF BASELINE
--
-- The current relational cell presheaf is Set-valued on all seven site
-- objects.  Every Set has a canonical equality/path groupoid.  Therefore the
-- full site admits a genuine discrete/equality-groupoid-valued baseline now,
-- with every restriction map acting functorially on equality morphisms.
--
-- This does NOT solve the transport-enrichment problem.  The existing cyclic
-- AB->BC->CA chart transitions are external cross-chart equivalences, while the
-- Grothendieck site contains no arrows edgeAB->edgeBC, edgeBC->edgeCA or
-- edgeCA->edgeAB.  Hence those C3 transitions are not site restrictions and
-- cannot be recovered merely by putting equality groupoids on the existing
-- fibres.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude

import DASHI.Core.RelationalSelfDescentExact as Existing
import DASHI.Core.RelationalTransportGroupoidActionExact as Groupoid
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf
import DASHI.Reasoning.TrialecticGrothendieckTransportCoherenceExact as Transport
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell

------------------------------------------------------------------------
-- 1. Equality groupoid in every section fibre.
------------------------------------------------------------------------

DiscreteHom :
  {U : Site.RelObj} →
  Presheaf.Section U →
  Presheaf.Section U →
  Set
DiscreteHom left right = left ≡ right

discreteId :
  {U : Site.RelObj}
  {x : Presheaf.Section U} →
  DiscreteHom x x
discreteId = refl

discreteCompose :
  {U : Site.RelObj}
  {x y z : Presheaf.Section U} →
  DiscreteHom y z →
  DiscreteHom x y →
  DiscreteHom x z
discreteCompose second first = trans first second

discreteInverse :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  DiscreteHom x y →
  DiscreteHom y x
discreteInverse = sym

discreteLeftIdentity :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : DiscreteHom x y) →
  discreteCompose discreteId f ≡ f
discreteLeftIdentity refl = refl

discreteRightIdentity :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : DiscreteHom x y) →
  discreteCompose f discreteId ≡ f
discreteRightIdentity refl = refl

discreteAssociative :
  {U : Site.RelObj}
  {w x y z : Presheaf.Section U} →
  (h : DiscreteHom y z) →
  (g : DiscreteHom x y) →
  (f : DiscreteHom w x) →
  discreteCompose h (discreteCompose g f)
  ≡ discreteCompose (discreteCompose h g) f
discreteAssociative refl refl refl = refl

discreteInverseLeft :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : DiscreteHom x y) →
  discreteCompose (discreteInverse f) f ≡ discreteId
discreteInverseLeft refl = refl

discreteInverseRight :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : DiscreteHom x y) →
  discreteCompose f (discreteInverse f) ≡ discreteId
discreteInverseRight refl = refl

------------------------------------------------------------------------
-- 2. Every site restriction is a functor on the equality groupoids.
------------------------------------------------------------------------

restrictDiscreteHom :
  {U V : Site.RelObj} →
  (change : Site.RelHom U V) →
  {x y : Presheaf.Section V} →
  DiscreteHom x y →
  DiscreteHom
    (Presheaf.restrict change x)
    (Presheaf.restrict change y)
restrictDiscreteHom change equality =
  cong (Presheaf.restrict change) equality

restrictDiscretePreservesIdentity :
  {U V : Site.RelObj} →
  (change : Site.RelHom U V) →
  {x : Presheaf.Section V} →
  restrictDiscreteHom change (discreteId {x = x})
  ≡ discreteId
restrictDiscretePreservesIdentity change = refl

restrictDiscretePreservesComposition :
  {U V : Site.RelObj} →
  (change : Site.RelHom U V) →
  {x y z : Presheaf.Section V} →
  (second : DiscreteHom y z) →
  (first : DiscreteHom x y) →
  restrictDiscreteHom change (discreteCompose second first)
  ≡
  discreteCompose
    (restrictDiscreteHom change second)
    (restrictDiscreteHom change first)
restrictDiscretePreservesComposition change refl refl = refl

restrictObjectsIdentity :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  Presheaf.restrict (Site.idR U) x ≡ x
restrictObjectsIdentity = Presheaf.restrictIdentity

restrictObjectsComposition :
  {U V W : Site.RelObj} →
  (second : Site.RelHom V W) →
  (first : Site.RelHom U V) →
  (x : Presheaf.Section W) →
  Presheaf.restrict (Site.composeRel second first) x
  ≡
  Presheaf.restrict first (Presheaf.restrict second x)
restrictObjectsComposition = Presheaf.restrictComposition

------------------------------------------------------------------------
-- 3. Exact obstruction: the C3 edge transitions are not arrows of this site.
------------------------------------------------------------------------

noSiteArrowABtoBC :
  Site.RelHom Site.edgeAB Site.edgeBC → ⊥
noSiteArrowABtoBC ()

noSiteArrowBCtoCA :
  Site.RelHom Site.edgeBC Site.edgeCA → ⊥
noSiteArrowBCtoCA ()

noSiteArrowCAtoAB :
  Site.RelHom Site.edgeCA Site.edgeAB → ⊥
noSiteArrowCAtoAB ()

externalABtoBCTransport :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchAB
    Existing.patchBC
externalABtoBCTransport = Transport.transportABtoBC

externalBCtoCATransport :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchBC
    Existing.patchCA
externalBCtoCATransport = Transport.transportBCtoCA

externalCAtoABTransport :
  Groupoid.RelTransportHom
    Cell.CellDialectic
    Existing.patchCA
    Existing.patchAB
externalCAtoABTransport = Transport.transportCAtoAB

------------------------------------------------------------------------
-- 4. Boundary: distinguish the paid discrete baseline from the desired
-- transport-enriched groupoid-valued presheaf.
------------------------------------------------------------------------

record TrialecticDiscreteGroupoidPresheafBaselineBoundary : Set where
  constructor trialectic-discrete-groupoid-presheaf-baseline-boundary
  field
    fullSiteDiscreteGroupoidBaselinePaid : Bool
    equalityGroupoidLawsPaid : Bool
    restrictionFunctorOnEqualityMorphismsPaid : Bool
    baseRestrictionIdentityCompositionReused : Bool
    externalC3EdgeTransportRetained : Bool
    edgeCycleIsSiteRestriction : Bool
    discreteBaselineCapturesC3Transport : Bool
    transportEnrichedGroupoidPresheafPaid : Bool

open TrialecticDiscreteGroupoidPresheafBaselineBoundary public

canonicalTrialecticDiscreteGroupoidPresheafBaselineBoundary :
  TrialecticDiscreteGroupoidPresheafBaselineBoundary
canonicalTrialecticDiscreteGroupoidPresheafBaselineBoundary =
  trialectic-discrete-groupoid-presheaf-baseline-boundary
    true true true true true false false false
