module DASHI.Physics.Closure.JSJBlockerNormalization where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.GeometryJSJAnalogueCrosswalk as Crosswalk
import DASHI.Physics.Closure.JSJAnaloguePieceClassification as JSJ

------------------------------------------------------------------------
-- Normalized blocker ledger for the JSJ/geometrization analogue crosswalk.
--
-- This module only normalizes blocker bookkeeping.  Every row keeps
-- dischargedHere = false, and the no-promotion witness is part of the row.
-- It does not promote BT or 369 candidate pieces to smooth JSJ data.

data BlockerScope : Set where
  btOnly :
    BlockerScope

  hyperfabric369Only :
    BlockerScope

  sharedBTAnd369 :
    BlockerScope

blockerLabel : JSJ.DecompositionBlocker → String
blockerLabel JSJ.noIncompressibleTorus =
  "no incompressible torus construction"
blockerLabel JSJ.noPrimeDecomposition =
  "no prime decomposition construction"
blockerLabel JSJ.noJSJUniqueness =
  "no JSJ uniqueness proof"
blockerLabel JSJ.noThurstonGeometrizationTheorem =
  "no Thurston geometrization theorem transfer"
blockerLabel JSJ.noSmoothThreeManifoldCarrier =
  "no smooth 3-manifold carrier"
blockerLabel JSJ.nonArchimedeanBoundaryMismatch =
  "non-Archimedean boundary mismatch"
blockerLabel JSJ.finiteHypercubeOnly =
  "finite hypercube carrier only"

smoothRequiredForBlocker : JSJ.DecompositionBlocker → Bool
smoothRequiredForBlocker JSJ.noIncompressibleTorus =
  true
smoothRequiredForBlocker JSJ.noPrimeDecomposition =
  true
smoothRequiredForBlocker JSJ.noJSJUniqueness =
  true
smoothRequiredForBlocker JSJ.noThurstonGeometrizationTheorem =
  true
smoothRequiredForBlocker JSJ.noSmoothThreeManifoldCarrier =
  true
smoothRequiredForBlocker JSJ.nonArchimedeanBoundaryMismatch =
  true
smoothRequiredForBlocker JSJ.finiteHypercubeOnly =
  true

record NormalizedJSJBlockerRow : Set where
  constructor normalizedJSJBlockerRow
  field
    blocker :
      JSJ.DecompositionBlocker

    label :
      String

    labelIsCanonical :
      label ≡ blockerLabel blocker

    smoothRequired :
      Bool

    smoothRequiredIsCanonical :
      smoothRequired ≡ smoothRequiredForBlocker blocker

    dischargedHere :
      Bool

    dischargedHereIsFalse :
      dischargedHere ≡ false

    notPromotedWitness :
      dischargedHere ≡ false

    scope :
      BlockerScope

open NormalizedJSJBlockerRow public

normalizedRow :
  JSJ.DecompositionBlocker →
  BlockerScope →
  NormalizedJSJBlockerRow
normalizedRow blocker scope =
  normalizedJSJBlockerRow
    blocker
    (blockerLabel blocker)
    refl
    (smoothRequiredForBlocker blocker)
    refl
    false
    refl
    refl
    scope

btNormalizedBlockerRows : List NormalizedJSJBlockerRow
btNormalizedBlockerRows =
  normalizedRow JSJ.noIncompressibleTorus sharedBTAnd369
  ∷ normalizedRow JSJ.noPrimeDecomposition sharedBTAnd369
  ∷ normalizedRow JSJ.noJSJUniqueness sharedBTAnd369
  ∷ normalizedRow JSJ.noThurstonGeometrizationTheorem sharedBTAnd369
  ∷ normalizedRow JSJ.noSmoothThreeManifoldCarrier sharedBTAnd369
  ∷ normalizedRow JSJ.nonArchimedeanBoundaryMismatch btOnly
  ∷ []

hyperfabric369NormalizedBlockerRows : List NormalizedJSJBlockerRow
hyperfabric369NormalizedBlockerRows =
  normalizedRow JSJ.noIncompressibleTorus sharedBTAnd369
  ∷ normalizedRow JSJ.noPrimeDecomposition sharedBTAnd369
  ∷ normalizedRow JSJ.noJSJUniqueness sharedBTAnd369
  ∷ normalizedRow JSJ.noThurstonGeometrizationTheorem sharedBTAnd369
  ∷ normalizedRow JSJ.noSmoothThreeManifoldCarrier sharedBTAnd369
  ∷ normalizedRow JSJ.finiteHypercubeOnly hyperfabric369Only
  ∷ []

normalizedUnionBlockerRows : List NormalizedJSJBlockerRow
normalizedUnionBlockerRows =
  normalizedRow JSJ.noIncompressibleTorus sharedBTAnd369
  ∷ normalizedRow JSJ.noPrimeDecomposition sharedBTAnd369
  ∷ normalizedRow JSJ.noJSJUniqueness sharedBTAnd369
  ∷ normalizedRow JSJ.noThurstonGeometrizationTheorem sharedBTAnd369
  ∷ normalizedRow JSJ.noSmoothThreeManifoldCarrier sharedBTAnd369
  ∷ normalizedRow JSJ.nonArchimedeanBoundaryMismatch btOnly
  ∷ normalizedRow JSJ.finiteHypercubeOnly hyperfabric369Only
  ∷ []

btCrosswalkBlockersAreSource :
  Crosswalk.blockers Crosswalk.btGeometryJSJCrosswalkRow
  ≡
  Crosswalk.btCrosswalkBlockers
btCrosswalkBlockersAreSource =
  refl

hyperfabric369CrosswalkBlockersAreSource :
  Crosswalk.blockers Crosswalk.hyperfabric369GeometryJSJCrosswalkRow
  ≡
  Crosswalk.hyperfabric369CrosswalkBlockers
hyperfabric369CrosswalkBlockersAreSource =
  refl

btBlockerCount : Nat
btBlockerCount =
  6

hyperfabric369BlockerCount : Nat
hyperfabric369BlockerCount =
  6

normalizedUnionBlockerCount : Nat
normalizedUnionBlockerCount =
  7

concatenatedCrosswalkBlockerCount : Nat
concatenatedCrosswalkBlockerCount =
  12

btBlockerCountIs6 :
  btBlockerCount ≡ 6
btBlockerCountIs6 =
  refl

hyperfabric369BlockerCountIs6 :
  hyperfabric369BlockerCount ≡ 6
hyperfabric369BlockerCountIs6 =
  refl

normalizedUnionBlockerCountIs7 :
  normalizedUnionBlockerCount ≡ 7
normalizedUnionBlockerCountIs7 =
  refl

concatenatedCrosswalkBlockerCountIs12 :
  concatenatedCrosswalkBlockerCount ≡ 12
concatenatedCrosswalkBlockerCountIs12 =
  refl

noIncompressibleTorusNotPromoted :
  dischargedHere
    (normalizedRow JSJ.noIncompressibleTorus sharedBTAnd369)
  ≡
  false
noIncompressibleTorusNotPromoted =
  refl

nonArchimedeanBoundaryMismatchNotPromoted :
  dischargedHere
    (normalizedRow JSJ.nonArchimedeanBoundaryMismatch btOnly)
  ≡
  false
nonArchimedeanBoundaryMismatchNotPromoted =
  refl

finiteHypercubeOnlyNotPromoted :
  dischargedHere
    (normalizedRow JSJ.finiteHypercubeOnly hyperfabric369Only)
  ≡
  false
finiteHypercubeOnlyNotPromoted =
  refl

record JSJBlockerNormalizationLedger : Set where
  constructor jsjBlockerNormalizationLedger
  field
    btCrosswalkRow :
      Crosswalk.GeometryJSJAnalogueCrosswalkRow

    btCrosswalkRowIsCanonical :
      btCrosswalkRow ≡ Crosswalk.btGeometryJSJCrosswalkRow

    btSourceBlockers :
      List JSJ.DecompositionBlocker

    btSourceBlockersAreCanonical :
      btSourceBlockers ≡ Crosswalk.btCrosswalkBlockers

    btRows :
      List NormalizedJSJBlockerRow

    btRowsAreCanonical :
      btRows ≡ btNormalizedBlockerRows

    btRowsCount :
      Nat

    btRowsCountIs6 :
      btRowsCount ≡ 6

    hyperfabric369CrosswalkRow :
      Crosswalk.GeometryJSJAnalogueCrosswalkRow

    hyperfabric369CrosswalkRowIsCanonical :
      hyperfabric369CrosswalkRow
      ≡
      Crosswalk.hyperfabric369GeometryJSJCrosswalkRow

    hyperfabric369SourceBlockers :
      List JSJ.DecompositionBlocker

    hyperfabric369SourceBlockersAreCanonical :
      hyperfabric369SourceBlockers
      ≡
      Crosswalk.hyperfabric369CrosswalkBlockers

    hyperfabric369Rows :
      List NormalizedJSJBlockerRow

    hyperfabric369RowsAreCanonical :
      hyperfabric369Rows ≡ hyperfabric369NormalizedBlockerRows

    hyperfabric369RowsCount :
      Nat

    hyperfabric369RowsCountIs6 :
      hyperfabric369RowsCount ≡ 6

    unionRows :
      List NormalizedJSJBlockerRow

    unionRowsAreCanonical :
      unionRows ≡ normalizedUnionBlockerRows

    unionRowsCount :
      Nat

    unionRowsCountIs7 :
      unionRowsCount ≡ 7

    concatenatedRowsCount :
      Nat

    concatenatedRowsCountIs12 :
      concatenatedRowsCount ≡ 12

    jsjTheoremAvailableHere :
      Bool

    jsjTheoremAvailableHereIsFalse :
      jsjTheoremAvailableHere ≡ false

open JSJBlockerNormalizationLedger public

canonicalJSJBlockerNormalizationLedger :
  JSJBlockerNormalizationLedger
canonicalJSJBlockerNormalizationLedger =
  jsjBlockerNormalizationLedger
    Crosswalk.btGeometryJSJCrosswalkRow
    refl
    Crosswalk.btCrosswalkBlockers
    refl
    btNormalizedBlockerRows
    refl
    btBlockerCount
    refl
    Crosswalk.hyperfabric369GeometryJSJCrosswalkRow
    refl
    Crosswalk.hyperfabric369CrosswalkBlockers
    refl
    hyperfabric369NormalizedBlockerRows
    refl
    hyperfabric369BlockerCount
    refl
    normalizedUnionBlockerRows
    refl
    normalizedUnionBlockerCount
    refl
    concatenatedCrosswalkBlockerCount
    refl
    false
    refl

canonicalLedgerKeepsJSJUnavailable :
  jsjTheoremAvailableHere canonicalJSJBlockerNormalizationLedger
  ≡
  false
canonicalLedgerKeepsJSJUnavailable =
  refl

