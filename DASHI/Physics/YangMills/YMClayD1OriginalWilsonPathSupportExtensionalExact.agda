module DASHI.Physics.YangMills.YMClayD1OriginalWilsonPathSupportExtensionalExact where

------------------------------------------------------------------------
-- Genuine original Wilson HOLONOMY locality, not merely support lists:
-- any two original link fields agreeing at every actually read
-- positive-bond variable give identical source path holonomy.
--
-- The path is the ACTUAL Balaban signed Wilson path; each negative
-- oriented step reads the positive link at the literal predecessor
-- site. The proof recurses over Bond.pathHolonomy itself.
--
-- Needed for D1 Gibbs conditional factorization and exact dependence
-- of the original four-bond plaquette action on its own source links.
--
-- Open: Fubini/disintegration, 6/18 degree, 19 quantitative packing,
-- original sparse mixed/frustrated polymers, E1/D2/N1/G1 Clay gates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Blocks
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Rooted
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

-- This is the literal underlying positive-bond *variable* used by the
-- actual oriented-link evaluator. Negative directions use the inverse
-- of the source positive variable at the actual negativeStep site.
sourceBondAtSignedStep :
  ∀ {n} → Blocks.PeriodicBlock n → Rooted.SignedAxis4 →
  Torus.PositiveBond (suc n)
sourceBondAtSignedStep site (Torus.pair axis true) =
  Torus.pair site axis
sourceBondAtSignedStep site (Torus.pair axis false) =
  Torus.pair (Bond.negativeStep site axis) axis

sourcePathPositiveBondSupport :
  ∀ {n} → Blocks.PeriodicBlock n → List Rooted.SignedAxis4 →
  List (Torus.PositiveBond (suc n))
sourcePathPositiveBondSupport site [] = []
sourcePathPositiveBondSupport site (direction ∷ directions) =
  sourceBondAtSignedStep site direction ∷
  sourcePathPositiveBondSupport
    (Bond.walkStep site direction) directions

-- Exact group-valued original positive/negative source-step locality.
originalOrientedLinkExtensional :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value}
    (left right : Bond.PeriodicBondField n Value)
    (site : Blocks.PeriodicBlock n)
    (direction : Rooted.SignedAxis4) →
  left (sourceBondAtSignedStep site direction)
    ≡ right (sourceBondAtSignedStep site direction) →
  Bond.orientedLinkBase group left site direction
    ≡ Bond.orientedLinkBase group right site direction
originalOrientedLinkExtensional left right site
  (Torus.pair axis true) same = same
originalOrientedLinkExtensional {group = group} left right site
  (Torus.pair axis false) same =
  cong (Bond.inverse group) same

-- All actual original source paths, not an assumed opaque cylinder.
originalPathHolonomyExtensional :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value}
    (left right : Bond.PeriodicBondGaugeRealization n Value group)
    (site : Blocks.PeriodicBlock n)
    (directions : List Rooted.SignedAxis4) →
  (∀ bond →
     Torus._∈_ bond (sourcePathPositiveBondSupport site directions) →
     Bond.bondField left bond ≡ Bond.bondField right bond) →
  Bond.pathHolonomy left site directions
    ≡ Bond.pathHolonomy right site directions
originalPathHolonomyExtensional left right site [] same =
  refl
originalPathHolonomyExtensional {group = group}
  left right site (direction ∷ directions) same =
  cong₂ (Bond.multiply group)
    (originalOrientedLinkExtensional
      (Bond.bondField left) (Bond.bondField right) site direction
      (same (sourceBondAtSignedStep site direction) Torus.here))
    (originalPathHolonomyExtensional
      left right (Bond.walkStep site direction) directions
      (λ bond member → same bond (Torus.there member)))

-- The actual original positive plaquette trace reads exactly the
-- positive-link slots of its literal four-step signed path.
sourcePlaquettePositiveBondSupport :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n) →
  List (Torus.PositiveBond (suc n))
sourcePlaquettePositiveBondSupport p =
  sourcePathPositiveBondSupport
    (Torus.first p)
    (Bond.plaquetteBoundaryDirections (Torus.second p))

sourceLength : ∀ {A : Set} → List A → Nat
sourceLength [] = 0
sourceLength (_ ∷ xs) = suc (sourceLength xs)

originalWilsonPlaquettePathReadsFourBondSlots :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n) →
  sourceLength (sourcePlaquettePositiveBondSupport p) ≡ 4
originalWilsonPlaquettePathReadsFourBondSlots p = refl

originalWilsonPlaquetteHolonomyExtensional :
  ∀ {n : Nat} {Value : Set} {group : Bond.ExactLinkGroup Value}
    (left right : Bond.PeriodicBondGaugeRealization n Value group)
    (p : Plaquette.PeriodicPlaquette n) →
  (∀ bond →
     Torus._∈_ bond (sourcePlaquettePositiveBondSupport p) →
     Bond.bondField left bond ≡ Bond.bondField right bond) →
  Bond.plaquetteHolonomyFromBonds left p
    ≡ Bond.plaquetteHolonomyFromBonds right p
originalWilsonPlaquetteHolonomyExtensional left right p same =
  originalPathHolonomyExtensional
    left right (Torus.first p)
    (Bond.plaquetteBoundaryDirections (Torus.second p)) same

-- This is stronger than a Boolean support test: source-true group
-- holonomies are proved equal for arbitrary nonabelian LinkGroup.
-- The selected SU(N) Wilson trace equality follows by congruence.
