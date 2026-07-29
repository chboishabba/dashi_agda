module DASHI.Physics.YangMills.BalabanClayGate4PeriodicReachCollarEnumerationExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _≤_)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Empty; Not; Dec; yes; no; _∈_; here; there)

import DASHI.Physics.YangMills.BalabanClayGate4FiniteEnlargementCollarOwnershipExact as Collar

------------------------------------------------------------------------
-- Primary provenance.
--
-- Tadeusz Bałaban, "Large Field Renormalization. I. The Basic Step of the
-- R Operation", Communications in Mathematical Physics 122 (1989), 175--202.
-- DOI: 10.1007/BF01257412.
--
-- Tadeusz Bałaban, "Large Field Renormalization. II. Localization,
-- Exponentiation, and Bounds for the R Operation", Communications in
-- Mathematical Physics 122 (1989), 355--392.
-- DOI: 10.1007/BF01238433.
--
-- Relationship: Bałaban owns the determining-set/enlargement architecture.
-- The bounded graph search, finite enumeration and collar partition below are
-- exact DASHI combinatorics over any finite block carrier.
------------------------------------------------------------------------

record FiniteReachCarrier (Block : Set) : Set₁ where
  field
    allBlocks : List Block
    allBlocksComplete : ∀ block → block ∈ allBlocks
    equalDecidable : ∀ left right → Dec (left ≡ right)
    Adjacent : Block → Block → Set
    adjacentDecidable : ∀ left right → Dec (Adjacent left right)

open FiniteReachCarrier public

data Any {A : Set} (P : A → Set) : List A → Set where
  anyHere : ∀ {value values} → P value → Any P (value ∷ values)
  anyThere : ∀ {value values} → Any P values → Any P (value ∷ values)

anyFromMembership :
  ∀ {A : Set} {P : A → Set} {value values} →
  value ∈ values → P value → Any P values
anyFromMembership here proof = anyHere proof
anyFromMembership (there member) proof = anyThere (anyFromMembership member proof)

decideAny :
  ∀ {A : Set} {P : A → Set} →
  (∀ value → Dec (P value)) →
  (values : List A) → Dec (Any P values)
decideAny decide [] = no (λ ())
decideAny decide (value ∷ values) with decide value
... | yes proof = yes (anyHere proof)
... | no notProof with decideAny decide values
... | yes rest = yes (anyThere rest)
... | no noRest = no reject
  where
  reject : Any _ (value ∷ values) → Empty
  reject (anyHere proof) = notProof proof
  reject (anyThere rest) = noRest rest

record StepCandidate {Block : Set}
    (dataSet : FiniteReachCarrier Block)
    (radius : Nat) (start finish middle : Block) : Set where
  constructor candidate
  field
    adjacent : Adjacent dataSet start middle
    reaches : Collar.ReachWithin (Adjacent dataSet) radius middle finish

open StepCandidate public

stepCandidateDecidable :
  ∀ {Block} (dataSet : FiniteReachCarrier Block)
    radius start finish middle →
  Dec (StepCandidate dataSet radius start finish middle)
stepCandidateDecidable dataSet radius start finish middle
  with adjacentDecidable dataSet start middle
... | no notAdjacent = no (λ value → notAdjacent (adjacent value))
... | yes adjacentProof
  with reachWithinDecidable dataSet radius middle finish
... | yes reachProof = yes (candidate adjacentProof reachProof)
... | no notReach = no (λ value → notReach (reaches value))

reachWithinDecidable :
  ∀ {Block} (dataSet : FiniteReachCarrier Block) →
  (radius : Nat) (start finish : Block) →
  Dec (Collar.ReachWithin (Adjacent dataSet) radius start finish)
reachWithinDecidable dataSet zero start finish
  with equalDecidable dataSet start finish
... | yes refl = yes Collar.stay
... | no notEqual = no reject
  where
  reject : Collar.ReachWithin (Adjacent dataSet) zero start finish → Empty
  reject Collar.stay = notEqual refl
reachWithinDecidable dataSet (suc radius) start finish
  with equalDecidable dataSet start finish
... | yes refl = yes Collar.stay
... | no notEqual
  with decideAny
    (stepCandidateDecidable dataSet radius start finish)
    (allBlocks dataSet)
... | yes witness = yes (assemble witness)
  where
  assemble :
    Any (StepCandidate dataSet radius start finish) (allBlocks dataSet) →
    Collar.ReachWithin (Adjacent dataSet) (suc radius) start finish
  assemble (anyHere value) =
    Collar.step (adjacent value) (reaches value)
  assemble (anyThere rest) = assemble rest
... | no noStep = no reject
  where
  reject :
    Collar.ReachWithin (Adjacent dataSet) (suc radius) start finish → Empty
  reject Collar.stay = notEqual refl
  reject (Collar.step {next = middle} adjacentProof reachProof) =
    noStep
      (anyFromMembership (allBlocksComplete dataSet middle)
        (candidate adjacentProof reachProof))

------------------------------------------------------------------------
-- Exact filtering and finite reach enumeration.
------------------------------------------------------------------------

filterDec :
  ∀ {A : Set} {P : A → Set} →
  (∀ value → Dec (P value)) → List A → List A
filterDec decide [] = []
filterDec decide (value ∷ values) with decide value
... | yes _ = value ∷ filterDec decide values
... | no _ = filterDec decide values

filterDecSound :
  ∀ {A : Set} {P : A → Set}
    (decide : ∀ value → Dec (P value)) {value values} →
  value ∈ filterDec decide values → P value
filterDecSound decide {values = []} ()
filterDecSound decide {value = value} {values = head ∷ values}
  with decide head
... | yes proof = λ where
    here → proof
    (there member) → filterDecSound decide member
... | no notProof = filterDecSound decide

filterDecComplete :
  ∀ {A : Set} {P : A → Set}
    (decide : ∀ value → Dec (P value)) {value values} →
  value ∈ values → P value → value ∈ filterDec decide values
filterDecComplete decide {values = []} () proof
filterDecComplete decide {value = value} {values = head ∷ values}
  member proof with decide head
... | yes selected with member
... | here = here
... | there tailMember = there (filterDecComplete decide tailMember proof)
... | no notSelected with member
... | here = notSelected proof
... | there tailMember = filterDecComplete decide tailMember proof

enumerateReachWithin :
  ∀ {Block} → FiniteReachCarrier Block → Nat → Block → List Block
enumerateReachWithin dataSet radius start =
  filterDec (reachWithinDecidable dataSet radius start) (allBlocks dataSet)

enumerateReachWithinSound :
  ∀ {Block} (dataSet : FiniteReachCarrier Block)
    radius start {finish} →
  finish ∈ enumerateReachWithin dataSet radius start →
  Collar.ReachWithin (Adjacent dataSet) radius start finish
enumerateReachWithinSound dataSet radius start =
  filterDecSound (reachWithinDecidable dataSet radius start)

enumerateReachWithinComplete :
  ∀ {Block} (dataSet : FiniteReachCarrier Block)
    radius start finish →
  Collar.ReachWithin (Adjacent dataSet) radius start finish →
  finish ∈ enumerateReachWithin dataSet radius start
enumerateReachWithinComplete dataSet radius start finish reach =
  filterDecComplete
    (reachWithinDecidable dataSet radius start)
    (allBlocksComplete dataSet finish)
    reach

------------------------------------------------------------------------
-- Finite region and enlargement enumeration.
------------------------------------------------------------------------

record FiniteRegionEnumeration (Block : Set) : Set₁ where
  field
    region : Collar.FiniteLargeFieldRegion Block
    regionBlocks : List Block
    regionSound : ∀ {block} → block ∈ regionBlocks → Collar.Contains region block
    regionComplete : ∀ block → Collar.Contains region block → block ∈ regionBlocks

open FiniteRegionEnumeration public

concatMap : ∀ {A B : Set} → (A → List B) → List A → List B
concatMap function [] = []
concatMap function (value ∷ values) =
  function value ++ concatMap function values
  where
  _++_ : List B → List B → List B
  [] ++ right = right
  (left ∷ rest) ++ right = left ∷ (rest ++ right)

record FinitePredicate (A : Set) (P : A → Set) : Set₁ where
  field
    elements : List A
    sound : ∀ {value} → value ∈ elements → P value
    complete : ∀ value → P value → value ∈ elements

open FinitePredicate public

record EnlargedEnumeration
    {Block : Set}
    (dataSet : FiniteReachCarrier Block)
    (regionData : FiniteRegionEnumeration Block)
    (radius : Nat) : Set₁ where
  field
    enumeration : FinitePredicate Block
      (Collar.Enlarged
        (record
          { Collar.EnlargementData.Adjacent = Adjacent dataSet
          ; Collar.EnlargementData.adjacentSymmetric = λ adjacent → adjacent
          })
        (region regionData) radius)

------------------------------------------------------------------------
-- A direct finite construction using the all-block enumeration.  This avoids
-- duplicate-sensitive concatenation: enumerate every torus block and filter by
-- the decidable enlarged predicate.
------------------------------------------------------------------------

record SymmetricFiniteReachCarrier (Block : Set) : Set₁ where
  field
    finiteReach : FiniteReachCarrier Block
    adjacentSymmetric : ∀ {left right} →
      Adjacent finiteReach left right → Adjacent finiteReach right left

open SymmetricFiniteReachCarrier public

enlargementData :
  ∀ {Block} → SymmetricFiniteReachCarrier Block → Collar.EnlargementData Block
enlargementData carrier = record
  { Collar.EnlargementData.Adjacent = Adjacent (finiteReach carrier)
  ; Collar.EnlargementData.adjacentSymmetric = adjacentSymmetric carrier
  }

enlargedDecidable :
  ∀ {Block} (carrier : SymmetricFiniteReachCarrier Block)
    (regionData : FiniteRegionEnumeration Block)
    radius block →
  Dec (Collar.Enlarged (enlargementData carrier)
    (region regionData) radius block)
enlargedDecidable carrier regionData radius block
  with decideAny decideSeed (regionBlocks regionData)
... | yes witness = yes (assemble witness)
  where
  decideSeed : ∀ seed → Dec
    (Collar.ReachWithin (Adjacent (finiteReach carrier)) radius seed block)
  decideSeed seed = reachWithinDecidable (finiteReach carrier) radius seed block

  assemble :
    Any (λ seed → Collar.ReachWithin
      (Adjacent (finiteReach carrier)) radius seed block)
      (regionBlocks regionData) →
    Collar.Enlarged (enlargementData carrier) (region regionData) radius block
  assemble (anyHere reach) =
    _ , (regionSound regionData here , reach)
  assemble (anyThere rest) with assemble rest
  ... | seed , (member , reach) =
    seed , (member , reach)
... | no noSeed = no reject
  where
  decideSeed : ∀ seed → Dec
    (Collar.ReachWithin (Adjacent (finiteReach carrier)) radius seed block)
  decideSeed seed = reachWithinDecidable (finiteReach carrier) radius seed block

  reject :
    Collar.Enlarged (enlargementData carrier) (region regionData) radius block → Empty
  reject (seed , (member , reach)) =
    noSeed
      (anyFromMembership (regionComplete regionData seed member) reach)

enlargedRegionFinite :
  ∀ {Block} (carrier : SymmetricFiniteReachCarrier Block)
    (regionData : FiniteRegionEnumeration Block) radius →
  FinitePredicate Block
    (Collar.Enlarged (enlargementData carrier)
      (region regionData) radius)
enlargedRegionFinite carrier regionData radius = record
  { elements = filterDec
      (enlargedDecidable carrier regionData radius)
      (allBlocks (finiteReach carrier))
  ; sound = filterDecSound
      (enlargedDecidable carrier regionData radius)
  ; complete = λ block proof →
      filterDecComplete
        (enlargedDecidable carrier regionData radius)
        (allBlocksComplete (finiteReach carrier) block)
        proof
  }

outerEnlargementPartition :
  ∀ {Block} (carrier : SymmetricFiniteReachCarrier Block)
    (regionData : FiniteRegionEnumeration Block)
    inner outer block →
  inner ≤ outer →
  Collar.Enlarged (enlargementData carrier)
    (region regionData) outer block →
  Collar.Enlarged (enlargementData carrier)
      (region regionData) inner block
  ⊎ Collar.Collar (enlargementData carrier)
      (region regionData) inner outer block
outerEnlargementPartition carrier regionData inner outer block inner≤outer outerMember
  with enlargedDecidable carrier regionData inner block
... | yes innerMember = inj₁ innerMember
... | no notInner = inj₂ (outerMember , notInner)

------------------------------------------------------------------------
-- Boundary support carrier: generation stores the proof that support lies in
-- the selected collar, so later R-operation consumers cannot lose ownership.
------------------------------------------------------------------------

record GeneratedBoundaryTerm
    {Term Block : Set}
    (supportData : Collar.LocalizedSupport Term Block)
    (enlargement : Collar.EnlargementData Block)
    (region : Collar.FiniteLargeFieldRegion Block)
    (inner outer : Nat)
    (term : Term) : Set where
  constructor generatedBoundary
  field
    supportInCollar :
      Collar.Every (Collar.Collar enlargement region inner outer)
        (Collar.support supportData term)

open GeneratedBoundaryTerm public

boundaryTermSupportInCollar :
  ∀ {Term Block}
    {supportData : Collar.LocalizedSupport Term Block}
    {enlargement : Collar.EnlargementData Block}
    {region : Collar.FiniteLargeFieldRegion Block}
    {inner outer term} →
  GeneratedBoundaryTerm supportData enlargement region inner outer term →
  Collar.Every (Collar.Collar enlargement region inner outer)
    (Collar.support supportData term)
boundaryTermSupportInCollar = supportInCollar

boundedReachDecisionLevel : ProofLevel
boundedReachDecisionLevel = machineChecked

finiteReachEnumerationLevel : ProofLevel
finiteReachEnumerationLevel = machineChecked

enlargedRegionFiniteEnumerationLevel : ProofLevel
enlargedRegionFiniteEnumerationLevel = machineChecked

outerEnlargementPartitionLevel : ProofLevel
outerEnlargementPartitionLevel = machineChecked

boundaryTermCollarOwnershipCarrierLevel : ProofLevel
boundaryTermCollarOwnershipCarrierLevel = machineChecked

literalPeriodicAdjacencyInstanceInputsLevel : ProofLevel
literalPeriodicAdjacencyInstanceInputsLevel = conditional

literalBadComponentFiniteEnumerationInputsLevel : ProofLevel
literalBadComponentFiniteEnumerationInputsLevel = conditional
