module DASHI.Reasoning.TrialecticWavePhaseGroupoidPresheafExact where

------------------------------------------------------------------------
-- FULL-SITE C3 WAVE-PHASE GROUPOID PRESHEAF
--
-- Base369WaveContinuousSymbolicCodingExact establishes the non-flattening
-- pattern used here: a symbolic/wave address is carried alongside the exact
-- payload rather than replacing it.  We apply that pattern categorically.
--
-- Objects are the existing exact site sections T18/T9/T3.  Morphisms retain
-- exact equality/observational evidence together with an independent C3 phase
-- in TriTruth.  The phase therefore supplies non-trivial automorphisms at all
-- seven site objects while restriction acts on the exact payload and preserves
-- the phase.  This avoids the old index mismatch between RelationalPatch and
-- RelObj without pretending chart rotation is a Grothendieck restriction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Base369 using (TriTruth; tri-low; tri-mid)

import DASHI.Foundations.Base369WaveContinuousSymbolicCodingExact as Wave
import DASHI.Foundations.Base369TriTruthField as Tri
import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.RelationalStageTwelveGrothendieckExtensionExact as Site
import DASHI.Reasoning.TrialecticGrothendieckCellPresheafExact as Presheaf
import DASHI.Reasoning.TrialecticThreeCellHyperformSynthesisExact as Cell
import DASHI.Reasoning.TrialecticSetEffectiveDescentExact as SetEffective

------------------------------------------------------------------------
-- 1. Wave-address calibration: C3 phase is a symbolic coordinate, and the
--    exact phase payload survives encode/decode exactly.
------------------------------------------------------------------------

phaseCoding : Wave.SymbolicCoding TriTruth
phaseCoding = Wave.symbolicCoding SSP.fromTriTruth

phaseEncodeDecode :
  (phase : TriTruth) →
  Wave.decode (Wave.encode phaseCoding phase) ≡ phase
phaseEncodeDecode = Wave.decodeAfterEncode phaseCoding

------------------------------------------------------------------------
-- 2. Local and global phase-labelled homs.
------------------------------------------------------------------------

record PhaseEqualityHom {A : Set} (x y : A) : Set where
  constructor phase-equality-hom
  field
    underlyingEquality : x ≡ y
    equalityPhase : TriTruth

open PhaseEqualityHom public

record GlobalPhaseHom
    (x y : Cell.CompatibleThreeCellTrialecticBoundary) : Set where
  constructor global-phase-hom
  field
    observationalEquality :
      SetEffective.BoundaryObservationalEquivalence x y
    globalPhase : TriTruth

open GlobalPhaseHom public

FibreHom :
  {U : Site.RelObj} →
  Presheaf.Section U →
  Presheaf.Section U →
  Set
FibreHom {Site.globalABC} x y = GlobalPhaseHom x y
FibreHom {Site.edgeAB} x y = PhaseEqualityHom x y
FibreHom {Site.edgeBC} x y = PhaseEqualityHom x y
FibreHom {Site.edgeCA} x y = PhaseEqualityHom x y
FibreHom {Site.vertexA} x y = PhaseEqualityHom x y
FibreHom {Site.vertexB} x y = PhaseEqualityHom x y
FibreHom {Site.vertexC} x y = PhaseEqualityHom x y

phaseOf :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  FibreHom x y → TriTruth
phaseOf {Site.globalABC} hom = globalPhase hom
phaseOf {Site.edgeAB} hom = equalityPhase hom
phaseOf {Site.edgeBC} hom = equalityPhase hom
phaseOf {Site.edgeCA} hom = equalityPhase hom
phaseOf {Site.vertexA} hom = equalityPhase hom
phaseOf {Site.vertexB} hom = equalityPhase hom
phaseOf {Site.vertexC} hom = equalityPhase hom

_≈ₚ_ :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  FibreHom x y → FibreHom x y → Set
f ≈ₚ g = phaseOf f ≡ phaseOf g

------------------------------------------------------------------------
-- 3. Groupoid operations.  Proof-bearing equality witnesses are intentionally
--    quotiented extensionally by phase, exactly as the existing transport
--    groupoid quotients proof/receipt-bearing records by forward action.
------------------------------------------------------------------------

identityHom :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  FibreHom x x
identityHom {Site.globalABC} x =
  global-phase-hom
    (SetEffective.boundary-observational-equivalence refl refl refl)
    Tri.triZero
identityHom {Site.edgeAB} x = phase-equality-hom refl Tri.triZero
identityHom {Site.edgeBC} x = phase-equality-hom refl Tri.triZero
identityHom {Site.edgeCA} x = phase-equality-hom refl Tri.triZero
identityHom {Site.vertexA} x = phase-equality-hom refl Tri.triZero
identityHom {Site.vertexB} x = phase-equality-hom refl Tri.triZero
identityHom {Site.vertexC} x = phase-equality-hom refl Tri.triZero

composeHom :
  {U : Site.RelObj}
  {x y z : Presheaf.Section U} →
  FibreHom y z →
  FibreHom x y →
  FibreHom x z
composeHom {Site.globalABC}
  (global-phase-hom yz pyz)
  (global-phase-hom xy pxy) =
  global-phase-hom
    (SetEffective.boundary-observational-equivalence
      (trans (SetEffective.sameAB xy) (SetEffective.sameAB yz))
      (trans (SetEffective.sameBC xy) (SetEffective.sameBC yz))
      (trans (SetEffective.sameCA xy) (SetEffective.sameCA yz)))
    (Tri.triAdd pyz pxy)
composeHom {Site.edgeAB}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)
composeHom {Site.edgeBC}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)
composeHom {Site.edgeCA}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)
composeHom {Site.vertexA}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)
composeHom {Site.vertexB}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)
composeHom {Site.vertexC}
  (phase-equality-hom yz pyz)
  (phase-equality-hom xy pxy) =
  phase-equality-hom (trans xy yz) (Tri.triAdd pyz pxy)

inverseHom :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  FibreHom x y →
  FibreHom y x
inverseHom {Site.globalABC} (global-phase-hom xy phase) =
  global-phase-hom
    (SetEffective.boundary-observational-equivalence
      (sym (SetEffective.sameAB xy))
      (sym (SetEffective.sameBC xy))
      (sym (SetEffective.sameCA xy)))
    (Tri.triNeg phase)
inverseHom {Site.edgeAB} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)
inverseHom {Site.edgeBC} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)
inverseHom {Site.edgeCA} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)
inverseHom {Site.vertexA} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)
inverseHom {Site.vertexB} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)
inverseHom {Site.vertexC} (phase-equality-hom xy phase) =
  phase-equality-hom (sym xy) (Tri.triNeg phase)

leftIdentity :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : FibreHom x y) →
  composeHom (identityHom y) f ≈ₚ f
leftIdentity f = Tri.triAdd-identityˡ (phaseOf f)

rightIdentity :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : FibreHom x y) →
  composeHom f (identityHom x) ≈ₚ f
rightIdentity f = Tri.triAdd-identityʳ (phaseOf f)

associative :
  {U : Site.RelObj}
  {w x y z : Presheaf.Section U} →
  (h : FibreHom y z) →
  (g : FibreHom x y) →
  (f : FibreHom w x) →
  composeHom h (composeHom g f)
  ≈ₚ
  composeHom (composeHom h g) f
associative h g f =
  Tri.triAdd-assoc (phaseOf h) (phaseOf g) (phaseOf f)

inverseAfterForward :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : FibreHom x y) →
  composeHom (inverseHom f) f ≈ₚ identityHom x
inverseAfterForward f = Tri.triAdd-inverseˡ (phaseOf f)

forwardAfterInverse :
  {U : Site.RelObj}
  {x y : Presheaf.Section U} →
  (f : FibreHom x y) →
  composeHom f (inverseHom f) ≈ₚ identityHom y
forwardAfterInverse f = Tri.triAdd-inverseʳ (phaseOf f)

------------------------------------------------------------------------
-- 4. Contravariant restriction functors on morphisms.
------------------------------------------------------------------------

restrictHom :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Presheaf.Section V} →
  FibreHom x y →
  FibreHom (Presheaf.restrict arrow x) (Presheaf.restrict arrow y)
restrictHom (Site.idR _) hom = hom

restrictHom Site.abToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (SetEffective.sameAB obs) phase
restrictHom Site.bcToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (SetEffective.sameBC obs) phase
restrictHom Site.caToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (SetEffective.sameCA obs) phase

restrictHom Site.aToAB (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.leftCell eq) phase
restrictHom Site.bToAB (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.rightCell eq) phase
restrictHom Site.bToBC (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.leftCell eq) phase
restrictHom Site.cToBC (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.rightCell eq) phase
restrictHom Site.cToCA (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.leftCell eq) phase
restrictHom Site.aToCA (phase-equality-hom eq phase) =
  phase-equality-hom (cong Cell.rightCell eq) phase

restrictHom Site.aToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (cong Cell.leftCell (SetEffective.sameAB obs)) phase
restrictHom Site.bToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (cong Cell.rightCell (SetEffective.sameAB obs)) phase
restrictHom Site.cToGlobal (global-phase-hom obs phase) =
  phase-equality-hom (cong Cell.rightCell (SetEffective.sameBC obs)) phase

restrictHomPreservesPhase :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y : Presheaf.Section V}
    (hom : FibreHom x y) →
  phaseOf (restrictHom arrow hom) ≡ phaseOf hom
restrictHomPreservesPhase (Site.idR _) hom = refl
restrictHomPreservesPhase Site.abToGlobal hom = refl
restrictHomPreservesPhase Site.bcToGlobal hom = refl
restrictHomPreservesPhase Site.caToGlobal hom = refl
restrictHomPreservesPhase Site.aToAB hom = refl
restrictHomPreservesPhase Site.bToAB hom = refl
restrictHomPreservesPhase Site.bToBC hom = refl
restrictHomPreservesPhase Site.cToBC hom = refl
restrictHomPreservesPhase Site.cToCA hom = refl
restrictHomPreservesPhase Site.aToCA hom = refl
restrictHomPreservesPhase Site.aToGlobal hom = refl
restrictHomPreservesPhase Site.bToGlobal hom = refl
restrictHomPreservesPhase Site.cToGlobal hom = refl

restrictIdentityHom :
  ∀ {U : Site.RelObj}
    {x y : Presheaf.Section U}
    (hom : FibreHom x y) →
  restrictHom (Site.idR U) hom ≈ₚ hom
restrictIdentityHom hom = restrictHomPreservesPhase (Site.idR _) hom

restrictCompositionHom :
  ∀ {U V W : Site.RelObj}
    (g : Site.RelHom V W)
    (f : Site.RelHom U V)
    {x y : Presheaf.Section W}
    (hom : FibreHom x y) →
  restrictHom (Site.composeRel g f) hom
  ≈ₚ
  restrictHom f (restrictHom g hom)
restrictCompositionHom g f hom =
  trans
    (restrictHomPreservesPhase (Site.composeRel g f) hom)
    (sym
      (trans
        (restrictHomPreservesPhase f (restrictHom g hom))
        (restrictHomPreservesPhase g hom)))

restrictPreservesIdentity :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    (x : Presheaf.Section V) →
  restrictHom arrow (identityHom x)
  ≈ₚ
  identityHom (Presheaf.restrict arrow x)
restrictPreservesIdentity arrow x =
  trans
    (restrictHomPreservesPhase arrow (identityHom x))
    refl

restrictPreservesComposition :
  ∀ {U V : Site.RelObj}
    (arrow : Site.RelHom U V)
    {x y z : Presheaf.Section V}
    (g : FibreHom y z)
    (f : FibreHom x y) →
  restrictHom arrow (composeHom g f)
  ≈ₚ
  composeHom (restrictHom arrow g) (restrictHom arrow f)
restrictPreservesComposition arrow g f =
  trans
    (restrictHomPreservesPhase arrow (composeHom g f))
    (sym
      (cong₂ Tri.triAdd
        (restrictHomPreservesPhase arrow g)
        (restrictHomPreservesPhase arrow f)))

------------------------------------------------------------------------
-- 5. Genuine non-discreteness at every site object.
------------------------------------------------------------------------

positivePhaseAutomorphism :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  FibreHom x x
positivePhaseAutomorphism {Site.globalABC} x =
  global-phase-hom
    (SetEffective.boundary-observational-equivalence refl refl refl)
    Tri.triOne
positivePhaseAutomorphism {Site.edgeAB} x = phase-equality-hom refl Tri.triOne
positivePhaseAutomorphism {Site.edgeBC} x = phase-equality-hom refl Tri.triOne
positivePhaseAutomorphism {Site.edgeCA} x = phase-equality-hom refl Tri.triOne
positivePhaseAutomorphism {Site.vertexA} x = phase-equality-hom refl Tri.triOne
positivePhaseAutomorphism {Site.vertexB} x = phase-equality-hom refl Tri.triOne
positivePhaseAutomorphism {Site.vertexC} x = phase-equality-hom refl Tri.triOne

positivePhaseDiffersFromIdentity :
  {U : Site.RelObj} →
  (x : Presheaf.Section U) →
  identityHom x ≈ₚ positivePhaseAutomorphism x → ⊥
positivePhaseDiffersFromIdentity x ()

record TrialecticWavePhaseGroupoidPresheafBoundary : Set where
  constructor trialectic-wave-phase-groupoid-presheaf-boundary
  field
    waveNonFlatteningPatternReused : Bool
    c3PhaseGroupLawReused : Bool
    allSevenSiteFibresCarryGroupoidHoms : Bool
    identityCompositionInversePaid : Bool
    groupoidLawsPaidModuloPhaseSetoid : Bool
    everyRestrictionHasMorphismFunctor : Bool
    restrictionIdentityCompositionPaid : Bool
    functorPreservesIdentityComposition : Bool
    nontrivialAutomorphismAtEverySiteObject : Bool
    chartTransitionIdentifiedWithRestriction : Bool
    fullSiteNonDiscreteGroupoidPresheafPaid : Bool

open TrialecticWavePhaseGroupoidPresheafBoundary public

canonicalTrialecticWavePhaseGroupoidPresheafBoundary :
  TrialecticWavePhaseGroupoidPresheafBoundary
canonicalTrialecticWavePhaseGroupoidPresheafBoundary =
  trialectic-wave-phase-groupoid-presheaf-boundary
    true true true true true true true true true false true
