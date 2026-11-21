module DASHI.Physics.YangMills.YMClayOriginalR445ReflectedPointwiseWordWeldExact where

------------------------------------------------------------------------
-- P0 / F0 source-owned R445 reflection field and Wilson WORD adapter.
--
-- This module consumes the ACTUAL original SU(N) bond field and original
-- SU(N) native positive two-link block: no parallel measure, graph, clock,
-- artificial gauge action, scalar or new Hamiltonian.
--
-- The original YMClayOriginalWilsonNativeOSPullbackExact interface
-- NativeBlockReflectsExactly universally quantifies over arbitrary
-- CoarseLinks -> real functions. The ORIGINAL existing source already
-- has the strictly constructive CoarsePointwiseObservable witness.
-- A pointwise blocked-field equality suffices for these genuine Wilson
-- words, avoiding unlicensed function extensionality.
--
-- The remaining ORIGINAL geometric bondwise reflection equality,
-- positive-time published Wilson RP and continuum D1/E1/D2 are named
-- source predicates; they are NOT supplied by this finite adapter.
-- Source-written, compiler/Agda kernel NOT independently checked.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; 1ℝ; _*ℝ_)

import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Torus
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN
import DASHI.Physics.YangMills.YMClaySUNMatrixNativeSignedWilsonExact as Signed
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicGibbsGaugeExact as Variable
import DASHI.Physics.YangMills.YMClaySUNNativeBlockedPositiveHolonomyExact as Native
import DASHI.Physics.YangMills.YMClaySUNMatrixWilsonTraceGaugeExact as Trace
import DASHI.Physics.YangMills.YMClayFiniteProductHaarPermutationExact as Haar
import DASHI.Physics.YangMills.YMClaySUNProductHaarGaugeFromOneLinkExact as Bilateral
import DASHI.Physics.Foundations.CMP119AntigravityRealGibbsDensityPositiveExact as Exp
import DASHI.Physics.YangMills.YMClaySUNSideFourBlockedFineHaarObservableExact as Word
import DASHI.Physics.YangMills.YMClaySUNVariablePeriodicBondPointwiseExact as Pointwise
import DASHI.Physics.YangMills.YMClayR445SelectedTimeReflectionForwardExact as Geometry
import DASHI.Physics.YangMills.BalabanClayGate4LiteralPeriodicPlaquetteWitnessExact as Plaquette

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
    (traceData : Trace.SUNMatrixRealTrace {Scalar = ℝ} theory)
    (exponential : Exp.StrictPositiveRealExponential)
    (betaFine : ℝ)
    (oneLink : Haar.OneLinkProductHaar (SUN.SUNMatrixElement theory))
    (bilateral : Bilateral.OneLinkSUNBilateralHaar theory oneLink)
    (divide : ℝ → ℝ → ℝ)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  originalGroup : Bond.ExactLinkGroup Link
  originalGroup = Signed.sunExactSignedLinkGroup theory

  FineLinks : Set
  FineLinks = Variable.SUNPeriodicLinks theory 3

  CoarseLinks : Set
  CoarseLinks = Variable.SUNPeriodicLinks theory 1

  -- The chosen physical reflection is t -> -t on the native
  -- side-four C4, and T -> -T on the side-two C2. Temporal
  -- link orientation is reversed, so the ORIGINAL group inverse
  -- and ORIGINAL native negativeStep must both be used.
  reflectOriginalFineLinks : FineLinks → FineLinks
  reflectOriginalFineLinks links
      (Torus.pair site Torus.zeroᵢ) =
    Bond.inverse originalGroup
      (links
        (Torus.pair
          (Bond.negativeStep
            (Geometry.reflectFineSite site) Torus.zeroᵢ)
          Torus.zeroᵢ))
  reflectOriginalFineLinks links
      (Torus.pair site (Torus.sucᵢ axis)) =
    links
      (Torus.pair
        (Geometry.reflectFineSite site)
        (Torus.sucᵢ axis))

  reflectOriginalCoarseLinks : CoarseLinks → CoarseLinks
  reflectOriginalCoarseLinks links
      (Torus.pair site Torus.zeroᵢ) =
    Bond.inverse originalGroup
      (links
        (Torus.pair
          (Bond.negativeStep
            (Geometry.reflectCoarseSite site) Torus.zeroᵢ)
          Torus.zeroᵢ))
  reflectOriginalCoarseLinks links
      (Torus.pair site (Torus.sucᵢ axis)) =
    links
      (Torus.pair
        (Geometry.reflectCoarseSite site)
        (Torus.sucᵢ axis))

  -- This is EXACTLY the original native SUN source block
  -- and its original non-Abelian length-two ordered holonomy.
  originalSourceR445Block : FineLinks → CoarseLinks
  originalSourceR445Block =
    Native.nativeSUNBlockLinks {m = 1} {l = 1} theory

  -- Decisive still-open geometry equality: on every ORIGINAL
  -- coarse bond; no function-valued equality and no arbitrary
  -- observable are assumed. All 64 cases have a finite
  -- noncommutative free-word reference test, but an actual
  -- Agda proof from the existing bond/step/origin definitions
  -- is still required to inhabit this type.
  NativeR445ReflectionPointwise : Set
  NativeR445ReflectionPointwise =
    (fine : FineLinks)
    (bond : Torus.PositiveBond 2) →
      originalSourceR445Block
        (reflectOriginalFineLinks fine) bond
      ≡
      reflectOriginalCoarseLinks
        (originalSourceR445Block fine) bond

  CoarsePointwiseObservable : (CoarseLinks → ℝ) → Set
  CoarsePointwiseObservable =
    Word.CoarsePointwiseObservable
      theory traceData exponential betaFine oneLink bilateral divide

  record OriginalWilsonPointwiseWord : Set where
    field
      observable : CoarseLinks → ℝ
      pointwise : CoarsePointwiseObservable observable

  open OriginalWilsonPointwiseWord public

  -- Structural word-algebra closure, using the ORIGINAL pre-existing
  -- CoarsePointwiseObservable rather than introducing a new axiom.
  unitWord : OriginalWilsonPointwiseWord
  unitWord = record
    { observable = λ links → 1ℝ
    ; pointwise = record { Word.sameAtAllBonds = λ left right eq → refl }
    }

  productWord :
    OriginalWilsonPointwiseWord →
    OriginalWilsonPointwiseWord →
    OriginalWilsonPointwiseWord
  productWord left right = record
    { observable =
        λ links → observable left links *ℝ observable right links
    ; pointwise = record
        { Word.sameAtAllBonds =
            λ a b same →
              cong₂ _*ℝ_
                (Word.sameAtAllBonds (pointwise left) a b same)
                (Word.sameAtAllBonds (pointwise right) a b same)
        }
    }

  orderedWord : List OriginalWilsonPointwiseWord →
    OriginalWilsonPointwiseWord
  orderedWord [] = unitWord
  orderedWord (head ∷ tail) =
    productWord head (orderedWord tail)

  -- Actual SOURCE OBLIGATION (bondwise equality) suffices for every
  -- product of source-owned pointwise-coherent Wilson tests.
  -- No function extensionality is imported or postulated.
  originalReflectedWordCommutesWithR445 :
    NativeR445ReflectionPointwise →
    (word : OriginalWilsonPointwiseWord) →
    (fine : FineLinks) →
      observable word
        (originalSourceR445Block (reflectOriginalFineLinks fine))
      ≡
      observable word
        (reflectOriginalCoarseLinks (originalSourceR445Block fine))
  originalReflectedWordCommutesWithR445 source sameWord fine =
    Word.sameAtAllBonds (pointwise sameWord)
      (originalSourceR445Block (reflectOriginalFineLinks fine))
      (reflectOriginalCoarseLinks (originalSourceR445Block fine))
      (source fine)

  originalReflectedAllWordsCommuteWithR445 :
    NativeR445ReflectionPointwise →
    (words : List OriginalWilsonPointwiseWord) →
    (fine : FineLinks) →
      observable (orderedWord words)
        (originalSourceR445Block (reflectOriginalFineLinks fine))
      ≡
      observable (orderedWord words)
        (reflectOriginalCoarseLinks (originalSourceR445Block fine))
  originalReflectedAllWordsCommuteWithR445 source words =
    originalReflectedWordCommutesWithR445 source (orderedWord words)


  -- SOURCE-WRITTEN ORIGINAL LOCAL SU(N) WILSON PLAQUETTE:
  -- This is literally the original periodicSUNPositivePlaquette followed
  -- by the original matrixWilsonValue (see originalLocalPlaquetteTraceAt
  -- in YMClayOriginalVariableWilsonCovarianceSourceExact).
  -- We now have a concrete inhabited original pointwise observable,
  -- rather than a generic oracle or a request for function extensionality.
  originalLocalPlaquetteWord :
    Plaquette.PeriodicPlaquette 1 → OriginalWilsonPointwiseWord
  originalLocalPlaquetteWord plaquette = record
    { observable = λ links →
        Trace.matrixWilsonValue traceData
          (Variable.periodicSUNPositivePlaquette theory 1 links plaquette)
    ; pointwise = record
        { Word.sameAtAllBonds = λ left right same →
            cong (Trace.matrixWilsonValue traceData)
              (Pointwise.variablePositivePlaquettePointwise
                theory 1 left right same plaquette)
        }
    }

  originalFinitePlaquetteWord :
    List (Plaquette.PeriodicPlaquette 1) →
    OriginalWilsonPointwiseWord
  originalFinitePlaquetteWord [] = unitWord
  originalFinitePlaquetteWord (plaquette ∷ others) =
    productWord (originalLocalPlaquetteWord plaquette)
      (originalFinitePlaquetteWord others)

  -- All finite original gauge-invariant plaquette words are now
  -- explicitly accepted by the constructive pointwise reflection adapter.
  originalActualPlaquetteWordsReflectThroughR445 :
    NativeR445ReflectionPointwise →
    (word : List (Plaquette.PeriodicPlaquette 1)) →
    (fine : FineLinks) →
      observable (originalFinitePlaquetteWord word)
        (originalSourceR445Block (reflectOriginalFineLinks fine))
      ≡
      observable (originalFinitePlaquetteWord word)
        (reflectOriginalCoarseLinks (originalSourceR445Block fine))
  originalActualPlaquetteWordsReflectThroughR445 source word =
    originalReflectedWordCommutesWithR445 source
      (originalFinitePlaquetteWord word)


  -- Pure original noncommutative two-link inversion. This is a valid
  -- symbolic identity for ANY original ExactLinkGroup, no commuting.
  reverseOriginalTwoLink :
    (u v : Link) →
    Bond.multiply originalGroup
      (Bond.inverse originalGroup v)
      (Bond.multiply originalGroup
        (Bond.inverse originalGroup u)
        (Bond.identity originalGroup))
    ≡
    Bond.inverse originalGroup
      (Bond.multiply originalGroup u
        (Bond.multiply originalGroup v
          (Bond.identity originalGroup)))
  reverseOriginalTwoLink u v =
    trans
      (cong
        (Bond.multiply originalGroup (Bond.inverse originalGroup v))
        (Bond.identityRight originalGroup (Bond.inverse originalGroup u)))
      (sym
        (trans
          (cong (Bond.inverse originalGroup)
            (cong (Bond.multiply originalGroup u)
              (Bond.identityRight originalGroup v)))
          (Bond.inverseProduct originalGroup u v)))

  sourceReflectedCoarsePredecessor :
    Geometry.CoarseSite → Geometry.CoarseSite
  sourceReflectedCoarsePredecessor site =
    Bond.negativeStep (Geometry.reflectCoarseSite site) Torus.zeroᵢ

  sourceBackwardTimeFirst : FineLinks → Geometry.CoarseSite → Link
  sourceBackwardTimeFirst fine site =
    fine
      (Torus.pair
        (Geometry.evenCoarseOrigin
          (sourceReflectedCoarsePredecessor site))
        Torus.zeroᵢ)

  sourceBackwardTimeSecond : FineLinks → Geometry.CoarseSite → Link
  sourceBackwardTimeSecond fine site =
    fine
      (Torus.pair
        (Bond.positiveStep
          (Geometry.evenCoarseOrigin
            (sourceReflectedCoarsePredecessor site))
          Torus.zeroᵢ)
        Torus.zeroᵢ)

  -- Candidate exact-source 8-case bond theorem, using 16-case
  -- ORIGINAL Fin.combine even-origin normal form from Geometry.
  -- Spatial cases are definitional after that rewrite; time cases
  -- are ONLY the original group inverse-of-ordered-product law.
  -- This proof candidate has NO postulates or placeholders.
  -- Agda typecheck is REQUIRED before marking the P0/F0 gate closed.
  originalNativeReflectionAtEveryBond :
    NativeR445ReflectionPointwise
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) Torus.zeroᵢ)
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z))
          | Geometry.originalR445NativeOriginIsEven originalGroup
              (sourceReflectedCoarsePredecessor (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z))) =
    reverseOriginalTwoLink
      (sourceBackwardTimeFirst fine (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)))
      (sourceBackwardTimeSecond fine (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)))
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) (Torus.sucᵢ Torus.zeroᵢ))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) =
    refl
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) =
    refl
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair Torus.zeroᵢ x) (Torus.pair y z)) =
    refl
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) Torus.zeroᵢ)
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z))
          | Geometry.originalR445NativeOriginIsEven originalGroup
              (sourceReflectedCoarsePredecessor (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z))) =
    reverseOriginalTwoLink
      (sourceBackwardTimeFirst fine (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)))
      (sourceBackwardTimeSecond fine (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)))
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) (Torus.sucᵢ Torus.zeroᵢ))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) =
    refl
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ)))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) =
    refl
  originalNativeReflectionAtEveryBond fine (Torus.pair (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) (Torus.sucᵢ (Torus.sucᵢ (Torus.sucᵢ Torus.zeroᵢ))))
    rewrite Geometry.originalR445NativeOriginIsEven originalGroup (Torus.pair (Torus.pair (Torus.sucᵢ Torus.zeroᵢ) x) (Torus.pair y z)) =
    refl

  -- No identification of the published positive-time word predicate,
  -- no Euclidean RP from positive Gibbs density, no continuum limit,
  -- and no Clay Yang-Mills mass gap are asserted here.
