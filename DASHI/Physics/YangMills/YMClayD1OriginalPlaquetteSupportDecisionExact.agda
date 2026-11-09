module DASHI.Physics.YangMills.YMClayD1OriginalPlaquetteSupportDecisionExact where

------------------------------------------------------------------------
-- Native ORIGINAL Wilson link-variable support decision.  No alternative
-- geometry, relabelled Gibbs measure, or physical assumption.
--
-- Reuse:
--  * BalabanPeriodicTorus4Carrier.PositiveBond / Dec equality;
--  * true PeriodicPlaquette from the varying-cutoff original action;
--  * originalFourPositiveBonds from the literal signed (+,+,-,-) loop.
--
-- Decides and supplies a proof of NO SHARED ORIGINAL LINK VARIABLES.
-- This is finite source combinatorics, NOT analytic Haar disintegration
-- or a physical full-Wilson CMP116 estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette
import DASHI.Physics.YangMills.YMClayD1OriginalPeriodicPlaquetteFourBondSupportExact as Source

Bond : Nat → Set
Bond n = Torus.PositiveBond (suc n)

bondEq :
  ∀ {n} (x y : Bond n) → Torus.Dec (x ≡ y)
bondEq {n} =
  Torus.productDecidableEquality
    (Torus.periodicTorus4DecidableEquality (suc n))
    Torus.cyclicIndexDecidableEquality

-- Finite decidable membership in the exact native original bond list.
decideBondIn :
  ∀ {n} (bond : Bond n) (bonds : List (Bond n)) →
  Torus.Dec (Torus._∈_ bond bonds)
decideBondIn bond [] =
  Torus.no (λ ())
decideBondIn bond (first ∷ others)
  with bondEq bond first
... | Torus.yes refl =
  Torus.yes Torus.here
... | Torus.no unequal
  with decideBondIn bond others
... | Torus.yes tailMember =
  Torus.yes (Torus.there tailMember)
... | Torus.no tailAbsent =
  Torus.no (λ { Torus.here → unequal refl
              ; (Torus.there tailMember) → tailAbsent tailMember })

-- Two supports are independent in the REFERENCE product-Haar variables
-- exactly when they have no shared original positive bond index.
SupportsDisjoint :
  ∀ {n} → List (Bond n) → List (Bond n) → Set
SupportsDisjoint left right =
  ∀ bond → Torus._∈_ bond left → Torus._∈_ bond right → Torus.Empty

decideSupportsDisjoint :
  ∀ {n} (left right : List (Bond n)) →
  Torus.Dec (SupportsDisjoint left right)
decideSupportsDisjoint [] right =
  Torus.yes (λ bond ())
decideSupportsDisjoint (first ∷ others) right
  with decideBondIn first right
... | Torus.yes inRight =
  Torus.no (λ disjoint → disjoint first Torus.here inRight)
... | Torus.no notRight
  with decideSupportsDisjoint others right
... | Torus.yes tailDisjoint =
  Torus.yes
    (λ { bond Torus.here inSecond → notRight inSecond
       ; bond (Torus.there inTail) inSecond →
           tailDisjoint bond inTail inSecond })
... | Torus.no notTailDisjoint =
  Torus.no
    (λ allDisjoint →
      notTailDisjoint
        (λ bond inTail inSecond →
          allDisjoint bond (Torus.there inTail) inSecond))

-- The ORIGINAL positive-plaquette supports as computed by the real
-- action's signed four-bond boundary, at every native changing cutoff.
OriginalPlaquettesDisjoint :
  ∀ {n} → Plaquette.PeriodicPlaquette n →
           Plaquette.PeriodicPlaquette n → Set
OriginalPlaquettesDisjoint p q =
  SupportsDisjoint
    (Source.originalFourPositiveBonds p)
    (Source.originalFourPositiveBonds q)

decideOriginalPlaquettesDisjoint :
  ∀ {n} (p q : Plaquette.PeriodicPlaquette n) →
  Torus.Dec (OriginalPlaquettesDisjoint p q)
decideOriginalPlaquettesDisjoint p q =
  decideSupportsDisjoint
    (Source.originalFourPositiveBonds p)
    (Source.originalFourPositiveBonds q)

-- The actual one-plaquette source always shares a positive link with
-- itself (the very first boundary slot).
originalPlaquetteNeverDisjointFromItself :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n) →
  OriginalPlaquettesDisjoint p p → Torus.Empty
originalPlaquetteNeverDisjointFromItself p disjoint =
  let head =
        Torus.pair
          (Torus.first p)
          (Torus.first (Plaquette.planeAxes (Torus.second p)))
  in disjoint head Torus.here Torus.here


------------------------------------------------------------------------
-- ACTUAL FINITE ORIGINAL FOUR-TORUS PLAQUETTE ENUMERATION.
-- Every source plaquette is in this list; incident support is computed
-- by filtering with a proof-producing positive-link membership decision.
-- This is NOT a user-selected subset and cannot be vacuously empty
-- when the original link has an actual incident plaquette.
------------------------------------------------------------------------

originalAllPlaquettes :
  (n : Nat) → List (Plaquette.PeriodicPlaquette n)
originalAllPlaquettes n =
  Torus.cartesian
    (Torus.elements (Torus.periodicTorus4Finite (suc n)))
    (Torus.allCyclicIndices Plaquette.six)

originalAllPlaquettesComplete :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n) →
  Torus._∈_ p (originalAllPlaquettes n)
originalAllPlaquettesComplete {n} p =
  Torus.cartesianMembership
    (Torus.complete (Torus.periodicTorus4Finite (suc n))
      (Torus.first p))
    (Torus.allCyclicIndicesComplete (Torus.second p))

originalIncidentPlaquettesFilter :
  ∀ {n} (bond : Bond n) →
  List (Plaquette.PeriodicPlaquette n) →
  List (Plaquette.PeriodicPlaquette n)
originalIncidentPlaquettesFilter bond [] = []
originalIncidentPlaquettesFilter bond (p ∷ rest)
  with decideBondIn bond (Source.originalFourPositiveBonds p)
... | Torus.yes _ = p ∷ originalIncidentPlaquettesFilter bond rest
... | Torus.no _ = originalIncidentPlaquettesFilter bond rest

originalIncidentPlaquettes :
  ∀ {n} (bond : Bond n) →
  List (Plaquette.PeriodicPlaquette n)
originalIncidentPlaquettes {n} bond =
  originalIncidentPlaquettesFilter bond (originalAllPlaquettes n)

-- Every output plaquette really has the original indicated positive
-- link among its four boundary variables, with a native membership
-- witness. No abstract incident-to-source bridge is postulated.
incidentFilterSound :
  ∀ {n} (bond : Bond n)
    (ps : List (Plaquette.PeriodicPlaquette n))
    (p : Plaquette.PeriodicPlaquette n) →
  Torus._∈_ p (originalIncidentPlaquettesFilter bond ps) →
  Torus._∈_ bond (Source.originalFourPositiveBonds p)
incidentFilterSound bond [] p ()
incidentFilterSound bond (first ∷ rest) p membership
  with decideBondIn bond (Source.originalFourPositiveBonds first)
... | Torus.yes member with membership
...   | Torus.here = member
...   | Torus.there tailMember =
      incidentFilterSound bond rest p tailMember
... | Torus.no _ =
      incidentFilterSound bond rest p membership

originalIncidentPlaquetteSound :
  ∀ {n} (bond : Bond n)
    (p : Plaquette.PeriodicPlaquette n) →
  Torus._∈_ p (originalIncidentPlaquettes bond) →
  Torus._∈_ bond (Source.originalFourPositiveBonds p)
originalIncidentPlaquetteSound {n} bond p =
  incidentFilterSound bond (originalAllPlaquettes n) p


------------------------------------------------------------------------
-- NONVACUOUS ORIGINAL LINK/PLAQUETTE INCIDENCE.
-- For every native positive link, choose one literal coordinate plane
-- that contains that link as a positive boundary variable.
------------------------------------------------------------------------

sourceCoveringPlane : Torus.Axis4 → Plaquette.PositivePlane4
sourceCoveringPlane Torus.zeroᵢ = Torus.zeroᵢ
sourceCoveringPlane (Torus.sucᵢ Torus.zeroᵢ) = Torus.zeroᵢ
sourceCoveringPlane (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.sucᵢ Torus.zeroᵢ
sourceCoveringPlane
  (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) =
  Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)

sourcePlaquetteContainingBond :
  ∀ {n} → Bond n → Plaquette.PeriodicPlaquette n
sourcePlaquetteContainingBond (Torus.pair site axis) =
  Torus.pair site (sourceCoveringPlane axis)

sourceCoveringPlaquetteActuallyContainsBond :
  ∀ {n} (bond : Bond n) →
  Torus._∈_ bond
    (Source.originalFourPositiveBonds
      (sourcePlaquetteContainingBond bond))
sourceCoveringPlaquetteActuallyContainsBond
  (Torus.pair site Torus.zeroᵢ) =
  Torus.here
sourceCoveringPlaquetteActuallyContainsBond
  (Torus.pair site (Torus.sucᵢ Torus.zeroᵢ)) =
  Torus.there (Torus.there (Torus.there Torus.here))
sourceCoveringPlaquetteActuallyContainsBond
  (Torus.pair site
    (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))) =
  Torus.there (Torus.there (Torus.there Torus.here))
sourceCoveringPlaquetteActuallyContainsBond
  (Torus.pair site
    (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))) =
  Torus.there (Torus.there (Torus.there Torus.here))

emptyElim : ∀ {A : Set} → Torus.Empty → A
emptyElim ()

incidentFilterComplete :
  ∀ {n} (bond : Bond n)
    (ps : List (Plaquette.PeriodicPlaquette n))
    (p : Plaquette.PeriodicPlaquette n) →
  Torus._∈_ p ps →
  Torus._∈_ bond (Source.originalFourPositiveBonds p) →
  Torus._∈_ p (originalIncidentPlaquettesFilter bond ps)
incidentFilterComplete bond [] p () bondMember
incidentFilterComplete bond (first ∷ rest) p Torus.here bondMember
  with decideBondIn bond (Source.originalFourPositiveBonds first)
... | Torus.yes _ = Torus.here
... | Torus.no absent = emptyElim (absent bondMember)
incidentFilterComplete bond (first ∷ rest) p
  (Torus.there inRest) bondMember
  with decideBondIn bond (Source.originalFourPositiveBonds first)
... | Torus.yes _ =
  Torus.there (incidentFilterComplete bond rest p inRest bondMember)
... | Torus.no _ =
  incidentFilterComplete bond rest p inRest bondMember

originalEveryPositiveLinkHasIncidentPlaquette :
  ∀ {n} (bond : Bond n) →
  Σ (Plaquette.PeriodicPlaquette n)
    (λ p → Torus._∈_ p (originalIncidentPlaquettes bond))
originalEveryPositiveLinkHasIncidentPlaquette {n} bond =
  sourcePlaquetteContainingBond bond ,
  incidentFilterComplete bond (originalAllPlaquettes n)
    (sourcePlaquetteContainingBond bond)
    (originalAllPlaquettesComplete (sourcePlaquetteContainingBond bond))
    (sourceCoveringPlaquetteActuallyContainsBond bond)

------------------------------------------------------------------------
-- Next source-native D1 proof:
-- 1. DONE SOURCE-WRITTEN: enumerate all original source plaquettes,
--    select genuinely incident plaquettes, prove soundness, and prove
--    one actually incident plaquette exists for every native bond.
-- 2. REMAINING: exactly-six incidence (for side >= 3), original
--    degree-18 plaquette conflict, and a source-native 19-packing proof.
-- 3. REMAINING: choose a full original link-set with disjoint incident
--    plaquette stars and prove source-specific packing witnesses.
-- 4. REMAINING: consume the actual original Wilson Gibbs product-Haar
--    Fubini/disintegration laws and the SU(2) coherent one-link bound.
-- 5. REMAINING PHYSICAL: sparse frustrated/mixed connected contour
--    suppression and full physical-distance CMP116 marked-source decay.
-- Agda 2.9 exact-head kernel acceptance has NOT been observed.
------------------------------------------------------------------------
