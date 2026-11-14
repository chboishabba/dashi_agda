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
-- ORIGINAL LINK-STAR CONFLICT / NO-CONFLICT DECISION.
-- A link conflict is actual common ORIGINAL plaquette membership,
-- not endpoint adjacency or disjointness of two plaquette boundaries.
------------------------------------------------------------------------

plaquetteEq :
  ∀ {n} (p q : Plaquette.PeriodicPlaquette n) →
  Torus.Dec (p ≡ q)
plaquetteEq {n} =
  Torus.productDecidableEquality
    (Torus.periodicTorus4DecidableEquality (suc n))
    Torus.cyclicIndexDecidableEquality

decidePlaquetteIn :
  ∀ {n} (p : Plaquette.PeriodicPlaquette n)
    (ps : List (Plaquette.PeriodicPlaquette n)) →
  Torus.Dec (Torus._∈_ p ps)
decidePlaquetteIn p [] = Torus.no (λ ())
decidePlaquetteIn p (q ∷ qs) with plaquetteEq p q
... | Torus.yes refl = Torus.yes Torus.here
... | Torus.no unequal with decidePlaquetteIn p qs
...   | Torus.yes member = Torus.yes (Torus.there member)
...   | Torus.no absent =
  Torus.no (λ { Torus.here → unequal refl
              ; (Torus.there member) → absent member })

OriginalStarsDisjoint :
  ∀ {n} → Bond n → Bond n → Set
OriginalStarsDisjoint a b =
  ∀ p →
  Torus._∈_ p (originalIncidentPlaquettes a) →
  Torus._∈_ p (originalIncidentPlaquettes b) →
  Torus.Empty

decideOriginalStarsDisjointOn :
  ∀ {n} (a b : Bond n)
    (as : List (Plaquette.PeriodicPlaquette n)) →
  Torus.Dec
    (∀ p → Torus._∈_ p as →
      Torus._∈_ p (originalIncidentPlaquettes b) → Torus.Empty)
decideOriginalStarsDisjointOn a b [] =
  Torus.yes (λ p ())
decideOriginalStarsDisjointOn a b (p ∷ rest)
  with decidePlaquetteIn p (originalIncidentPlaquettes b)
... | Torus.yes present =
  Torus.no (λ separate → separate p Torus.here present)
... | Torus.no absent with decideOriginalStarsDisjointOn a b rest
...   | Torus.yes tailSeparate =
  Torus.yes
    (λ { p Torus.here inB → absent inB
       ; p (Torus.there inRest) inB →
           tailSeparate p inRest inB })
...   | Torus.no notTail =
  Torus.no
    (λ allSeparate →
      notTail
        (λ p inRest inB →
          allSeparate p (Torus.there inRest) inB))

decideOriginalStarsDisjoint :
  ∀ {n} (a b : Bond n) →
  Torus.Dec (OriginalStarsDisjoint a b)
decideOriginalStarsDisjoint a b =
  decideOriginalStarsDisjointOn a b (originalIncidentPlaquettes a)

-- Actual self-conflict is constructively proved using the real
-- nonempty source incidence, not an assumed reflexivity axiom.
originalStarNeverDisjointFromItself :
  ∀ {n} (bond : Bond n) →
  OriginalStarsDisjoint bond bond → Torus.Empty
originalStarNeverDisjointFromItself bond separate with
  originalEveryPositiveLinkHasIncidentPlaquette bond
... | p , member = separate p member member

-- Reversing link order does not change the original star-separation.
originalStarsDisjointSymmetric :
  ∀ {n} {a b : Bond n} →
  OriginalStarsDisjoint a b → OriginalStarsDisjoint b a
originalStarsDisjointSymmetric separate p inB inA =
  separate p inA inB


------------------------------------------------------------------------
-- CONSTRUCTIVE ORIGINAL LINK-STAR GREEDY PACKING.
-- This is the genuine independent plaquette-star set computed from
-- native source links, with a PROOF of independence and subset.
-- The quantitative 19-packing lower cardinal bound still requires
-- the actual degree-18 finite combinatorics lemma.
------------------------------------------------------------------------

filterOriginalStarFree :
  ∀ {n} (a : Bond n) → List (Bond n) → List (Bond n)
filterOriginalStarFree a [] = []
filterOriginalStarFree a (b ∷ bs)
  with decideOriginalStarsDisjoint a b
... | Torus.yes _ = b ∷ filterOriginalStarFree a bs
... | Torus.no _ = filterOriginalStarFree a bs

filterOriginalStarFreeSubset :
  ∀ {n} (a : Bond n) (bs : List (Bond n)) →
  ∀ {b} → Torus._∈_ b (filterOriginalStarFree a bs) →
  Torus._∈_ b bs
filterOriginalStarFreeSubset a [] ()
filterOriginalStarFreeSubset a (b ∷ bs) member
  with decideOriginalStarsDisjoint a b
... | Torus.yes _ with member
...   | Torus.here = Torus.here
...   | Torus.there tailMember =
      Torus.there (filterOriginalStarFreeSubset a bs tailMember)
... | Torus.no _ =
  Torus.there (filterOriginalStarFreeSubset a bs member)

filterOriginalStarFreeSound :
  ∀ {n} (a : Bond n) (bs : List (Bond n))
    (b : Bond n) →
  Torus._∈_ b (filterOriginalStarFree a bs) →
  OriginalStarsDisjoint a b
filterOriginalStarFreeSound a [] b ()
filterOriginalStarFreeSound a (first ∷ rest) b member
  with decideOriginalStarsDisjoint a first
... | Torus.yes separate with member
...   | Torus.here = separate
...   | Torus.there tailMember =
      filterOriginalStarFreeSound a rest b tailMember
... | Torus.no _ =
  filterOriginalStarFreeSound a rest b member

-- The greedy procedure is genuinely executable on any finite list of
-- literal native 4D Wilson positive links, including duplicates.
greedyOriginalDisjointStars :
  ∀ {n} → List (Bond n) → List (Bond n)
greedyOriginalDisjointStars [] = []
greedyOriginalDisjointStars (a ∷ as) =
  a ∷ greedyOriginalDisjointStars (filterOriginalStarFree a as)

greedyOriginalDisjointStarsSubset :
  ∀ {n} (as : List (Bond n)) (b : Bond n) →
  Torus._∈_ b (greedyOriginalDisjointStars as) →
  Torus._∈_ b as
greedyOriginalDisjointStarsSubset [] b ()
greedyOriginalDisjointStarsSubset (a ∷ as) b Torus.here =
  Torus.here
greedyOriginalDisjointStarsSubset (a ∷ as) b
  (Torus.there inTail) =
  Torus.there
    (filterOriginalStarFreeSubset a as
      (greedyOriginalDisjointStarsSubset
        (filterOriginalStarFree a as) b inTail))

data AllOriginalStarsIndependent {n} :
    List (Bond n) → Set where
  noStars : AllOriginalStarsIndependent []
  addFreeStar :
    ∀ {a bs} →
    (∀ b → Torus._∈_ b bs → OriginalStarsDisjoint a b) →
    AllOriginalStarsIndependent bs →
    AllOriginalStarsIndependent (a ∷ bs)

greedyOriginalDisjointStarsIndependent :
  ∀ {n} (as : List (Bond n)) →
  AllOriginalStarsIndependent (greedyOriginalDisjointStars as)
greedyOriginalDisjointStarsIndependent [] = noStars
greedyOriginalDisjointStarsIndependent (a ∷ as) =
  addFreeStar
    (λ b member →
      filterOriginalStarFreeSound a as b
        (greedyOriginalDisjointStarsSubset
          (filterOriginalStarFree a as) b member))
    (greedyOriginalDisjointStarsIndependent
      (filterOriginalStarFree a as))


------------------------------------------------------------------------
-- SOURCE-TRUE GREEDY MAXIMALITY: Every ORIGINAL marked link is
-- chosen or actually conflicts with a chosen source link.
-- This pays the dominating-set combinatorial theorem, without
-- assuming the still-unproved literal degree-18 incidence bound.
------------------------------------------------------------------------

open import Data.Sum using (_⊎_; inj₁; inj₂)

filterOriginalStarFreeComplete :
  ∀ {n} (a : Bond n) (as : List (Bond n))
    (b : Bond n) →
  Torus._∈_ b as →
  OriginalStarsDisjoint a b →
  Torus._∈_ b (filterOriginalStarFree a as)
filterOriginalStarFreeComplete a [] b () separate
filterOriginalStarFreeComplete a (first ∷ rest) b
  Torus.here separate
  with decideOriginalStarsDisjoint a first
... | Torus.yes _ = Torus.here
... | Torus.no notSeparate = emptyElim (notSeparate separate)
filterOriginalStarFreeComplete a (first ∷ rest) b
  (Torus.there inTail) separate
  with decideOriginalStarsDisjoint a first
... | Torus.yes _ =
  Torus.there (filterOriginalStarFreeComplete a rest b inTail separate)
... | Torus.no _ =
  filterOriginalStarFreeComplete a rest b inTail separate

OriginalStarDominated :
  ∀ {n} (b : Bond n) → List (Bond n) → Set
OriginalStarDominated {n} b selected =
  Torus._∈_ b selected ⊎
  Σ (Bond n)
    (λ chosen →
      Torus.Product
        (Torus._∈_ chosen selected)
        (OriginalStarsDisjoint chosen b → Torus.Empty))

greedyOriginalDisjointStarsMaximal :
  ∀ {n} (marked : List (Bond n)) (b : Bond n) →
  Torus._∈_ b marked →
  OriginalStarDominated b (greedyOriginalDisjointStars marked)
greedyOriginalDisjointStarsMaximal [] b ()
greedyOriginalDisjointStarsMaximal (a ∷ as) b Torus.here =
  inj₁ Torus.here
greedyOriginalDisjointStarsMaximal (a ∷ as) b
  (Torus.there inInput)
  with decideOriginalStarsDisjoint a b
... | Torus.no conflict =
  inj₂ (a , Torus.pair Torus.here conflict)
... | Torus.yes separate
  with greedyOriginalDisjointStarsMaximal
    (filterOriginalStarFree a as) b
    (filterOriginalStarFreeComplete a as b inInput separate)
... | inj₁ selected =
  inj₁ (Torus.there selected)
... | inj₂ (chosen , witness) =
  inj₂ (chosen ,
    Torus.pair
      (Torus.there (Torus.first witness))
      (Torus.second witness))

------------------------------------------------------------------------
-- Next source-native D1 proof:
-- 1. DONE SOURCE-WRITTEN: enumerate all original source plaquettes,
--    select genuinely incident plaquettes, prove soundness, and prove
--    one actually incident plaquette exists for every native bond.
-- 2. DONE SOURCE-WRITTEN: proof-producing decision whether two\n--    actual source link stars share an original plaquette, with\n--    constructive nonempty self-conflict and symmetry.\n-- 3. REMAINING: exactly-six incidence (for side >= 3), original
--    degree-18 plaquette conflict, and a source-native 19-packing proof.
-- 4. DONE SOURCE-WRITTEN: compute a greedy actually source-star\n--    independent subset and prove independence + input membership,\n--    plus exact maximality: each unchosen original link conflicts\n--    with one genuinely selected original source link.\n--    REMAINING: the original degree-18 quantitative 19-packing bound.
-- 5. REMAINING: consume the actual original Wilson Gibbs product-Haar
--    Fubini/disintegration laws and the SU(2) coherent one-link bound.
-- 6. REMAINING PHYSICAL: sparse frustrated/mixed connected contour
--    suppression and full physical-distance CMP116 marked-source decay.
-- Agda 2.9 exact-head kernel acceptance has NOT been observed.
------------------------------------------------------------------------
