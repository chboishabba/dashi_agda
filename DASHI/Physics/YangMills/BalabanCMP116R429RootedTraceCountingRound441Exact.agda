{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R429RootedTraceCountingRound441Exact where

------------------------------------------------------------------------
-- B / ROUND441: R429 DOMAIN -> CANONICAL ROOTED TRACE -> 8^d SHELL COUNT
--
-- The literal CMP116 localization-domain family is finite at each cutoff.
-- To pay the (1.26)--(1.28) entropy bill we do not assume the final weighted
-- sum.  Instead a source implementation supplies:
--
--   * a canonical signed-direction trace word for each retained R429 domain;
--   * injectivity of that trace encoding;
--   * a duplicate-free list of the domains of each exact tree depth;
--   * the finite partition of localizedDomains by those depth shells.
--
-- The repository's exact eight-direction word enumeration then gives
--
--     |S_d| <= 8^d
--
-- mechanically.  This is the precise combinatorial bridge needed before the
-- residual source decay is spent on the geometric series.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_≤_)
open import Data.List.Base using (List; []; _∷_; _++_; length)
open import Data.Rational.Base as ℚ using (ℚ)
open import Data.Product using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.GraphCombinatorics as GC
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Periodic
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Trace
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429

------------------------------------------------------------------------
-- Small list lemmas on GraphCombinatorics' membership carrier.
------------------------------------------------------------------------

mapMemberReflect :
  ∀ {A B : Set} {f : A → B} {x : A} {xs : List A} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  f x GC.∈ GC.mapList f xs →
  x GC.∈ xs
mapMemberReflect {xs = []} injective ()
mapMemberReflect {f = f} {x = x} {xs = y ∷ ys} injective GC.here =
  subst
    (λ selected → selected GC.∈ y ∷ ys)
    (sym (injective refl))
    GC.here
mapMemberReflect {f = f} {x = x} {xs = y ∷ ys}
    injective (GC.there membership) =
  GC.there (mapMemberReflect injective membership)

mapNoDuplicates :
  ∀ {A B : Set} {f : A → B} {xs : List A} →
  (∀ {left right} → f left ≡ f right → left ≡ right) →
  GC.NoDuplicates xs →
  GC.NoDuplicates (GC.mapList f xs)
mapNoDuplicates injective GC.noDup-nil = GC.noDup-nil
mapNoDuplicates {f = f} injective
    (GC.noDup-cons headFresh tailUnique) =
  GC.noDup-cons
    (λ mappedMembership →
      headFresh (mapMemberReflect injective mappedMembership))
    (mapNoDuplicates injective tailUnique)

periodicMembershipToGraph :
  ∀ {A : Set} {x : A} {xs : List A} →
  x Periodic.∈ xs →
  x GC.∈ xs
periodicMembershipToGraph Periodic.here = GC.here
periodicMembershipToGraph (Periodic.there membership) =
  GC.there (periodicMembershipToGraph membership)

mapListMembershipSource :
  ∀ {A B : Set} {f : A → B} {xs : List A} {y : B} →
  y GC.∈ GC.mapList f xs →
  Σ A (λ x → x GC.∈ xs × y ≡ f x)
mapListMembershipSource {xs = []} ()
mapListMembershipSource {xs = x ∷ xs} GC.here =
  x , (GC.here , refl)
mapListMembershipSource {xs = x ∷ xs} (GC.there membership)
  with mapListMembershipSource membership
... | source , (sourceMembership , equality) =
  source , (GC.there sourceMembership , equality)

------------------------------------------------------------------------
-- Finite depth partition.
------------------------------------------------------------------------

flattenDepthShells : ∀ {A : Set} → (Nat → List A) → Nat → List A
flattenDepthShells shells zero = shells zero
flattenDepthShells shells (suc depth) =
  flattenDepthShells shells depth ++ shells (suc depth)

record R429RootedTraceShellEncoding
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (domainTreeDistance : R429.Domain fourStage → Nat)
    : Set₁ where
  field
    traceEncoding :
      Trace.PhysicalPolymerTraceEncoding (R429.Domain fourStage)

    traceSizeIsDomainTreeDistance :
      ∀ domain →
      Trace.polymerSize traceEncoding domain
      ≡ domainTreeDistance domain

    domainsAtDepth : Nat → List (R429.Domain fourStage)

    domainsAtDepthNoDuplicates :
      ∀ depth → GC.NoDuplicates (domainsAtDepth depth)

    domainsAtDepthExact :
      ∀ depth {domain} →
      domain GC.∈ domainsAtDepth depth →
      domainTreeDistance domain ≡ depth

    terminalDepth : Nat

    localizedDomainsAreDepthPartition :
      R429.localizedDomains fourStage
      ≡ flattenDepthShells domainsAtDepth terminalDepth

open R429RootedTraceShellEncoding public

traceWord :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance} →
  R429RootedTraceShellEncoding
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage domainTreeDistance →
  R429.Domain fourStage → List Trace.SignedAxis4
traceWord encoding =
  Trace.canonicalTraceWord (traceEncoding encoding)

traceWordInjective :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance}
    (encoding :
      R429RootedTraceShellEncoding
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage domainTreeDistance) →
  ∀ {left right} →
  traceWord encoding left ≡ traceWord encoding right →
  left ≡ right
traceWordInjective encoding =
  Trace.traceEncodingInjective (traceEncoding encoding)

mappedTraceWordsNoDuplicates :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance}
    (encoding :
      R429RootedTraceShellEncoding
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage domainTreeDistance)
    depth →
  GC.NoDuplicates
    (GC.mapList (traceWord encoding) (domainsAtDepth encoding depth))
mappedTraceWordsNoDuplicates encoding depth =
  mapNoDuplicates
    (traceWordInjective encoding)
    (domainsAtDepthNoDuplicates encoding depth)

mappedTraceWordsSubsetEnumeration :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance}
    (encoding :
      R429RootedTraceShellEncoding
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage domainTreeDistance)
    depth →
  GC._⊆_
    (GC.mapList (traceWord encoding) (domainsAtDepth encoding depth))
    (Trace.allSignedWords depth)
mappedTraceWordsSubsetEnumeration encoding depth {word} membership
  with mapListMembershipSource membership
... | domain , (domainMembership , refl) =
  let
    wordLengthAtDomainSize :
      length (traceWord encoding domain)
      ≡ Trace.polymerSize (traceEncoding encoding) domain
    wordLengthAtDomainSize =
      Trace.canonicalTraceLength (traceEncoding encoding) domain

    domainSizeAtDepth :
      Trace.polymerSize (traceEncoding encoding) domain ≡ depth
    domainSizeAtDepth =
      trans
        (traceSizeIsDomainTreeDistance encoding domain)
        (domainsAtDepthExact encoding depth domainMembership)

    wordLengthAtDepth :
      length (traceWord encoding domain) ≡ depth
    wordLengthAtDepth =
      trans wordLengthAtDomainSize domainSizeAtDepth
  in
  periodicMembershipToGraph
    (Trace.allSignedWordsComplete
      (traceWord encoding domain)
      wordLengthAtDepth)

domainShellCardinalityBelowEightPower :
  ∀ {Measure TestObservable dataSet extension base fourStage domainTreeDistance}
    (encoding :
      R429RootedTraceShellEncoding
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage domainTreeDistance)
    depth →
  length (domainsAtDepth encoding depth) ≤ Trace.pow8 depth
domainShellCardinalityBelowEightPower encoding depth =
  subst
    (λ mappedLength →
      mappedLength ≤ Trace.pow8 depth)
    (sym
      (GC.listMapLength
        (traceWord encoding)
        (domainsAtDepth encoding depth)))
    (subst
      (λ targetLength →
        length
          (GC.mapList
            (traceWord encoding)
            (domainsAtDepth encoding depth))
        ≤ targetLength)
      (Trace.allSignedWordsLength depth)
      (GC.noDupSubsetLength≤
        (mappedTraceWordsNoDuplicates encoding depth)
        (mappedTraceWordsSubsetEnumeration encoding depth)))

round441InjectiveTraceShellCountCompilerLevel : ProofLevel
round441InjectiveTraceShellCountCompilerLevel = machineChecked

-- This is now the exact R429 combinatorial/source geometry seam:
-- construct the canonical trace encoding and finite depth partition for the
-- literal localization domains.  The 8^d cardinality theorem is downstream.
literalRound441R429RootedTraceEncodingLevel : ProofLevel
literalRound441R429RootedTraceEncodingLevel = conditional
