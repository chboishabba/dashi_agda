module DASHI.Physics.Closure.G3P2OperatorSurface where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Process.DASHIMarkovCompatibility as DMC
import DASHI.Physics.Closure.G3PoincareGalileiCarrierChain as G3
import Ontology.GodelLattice as GL

------------------------------------------------------------------------
-- G3 p2 operator package, conditional on the projection adapter.
--
-- This module deliberately does not construct a FactorVec projection from
-- DASHIState.  Everything below is parameterized by the existing minimal
-- adapter surface from G3PoincareGalileiCarrierChain.

data G3P2OperatorSurfaceStatus : Set where
  conditionalP2OperatorSurfaceOnlyNoPromotion :
    G3P2OperatorSurfaceStatus

data G3P2BumpKind : Set where
  p2PrimeBump :
    G3P2BumpKind

  spatialBump :
    G3P2BumpKind

data G3P2MomentumGenerator : Set where
  p2Momentum :
    G3P2MomentumGenerator

  spatialMomentum :
    G3P2MomentumGenerator

data G3P2BoostGenerator : Set where
  p2Boost :
    G3P2BoostGenerator

  spatialBoost :
    G3P2BoostGenerator

data G3P2NamedOperator : Set where
  pOperator :
    G3P2NamedOperator

  hOperator :
    G3P2NamedOperator

  kOperator :
    G3P2NamedOperator

data G3P2OperatorMissingPiece : Set where
  missingSpatialBumpState :
    G3P2OperatorMissingPiece

  missingPActionLaw :
    G3P2OperatorMissingPiece

  missingHActionLaw :
    G3P2OperatorMissingPiece

  missingKActionLaw :
    G3P2OperatorMissingPiece

  missingPKCommutatorLaw :
    G3P2OperatorMissingPiece

  missingPHCommutatorLaw :
    G3P2OperatorMissingPiece

  missingKHCommutatorLaw :
    G3P2OperatorMissingPiece

  missingPPCommutatorLaw :
    G3P2OperatorMissingPiece

  missingKKCommutatorLaw :
    G3P2OperatorMissingPiece

  missingFilteredCommutatorCompatibility :
    G3P2OperatorMissingPiece

  missingIWContractionParameterLaw :
    G3P2OperatorMissingPiece

  missingPoincareAtP2PromotionWitness :
    G3P2OperatorMissingPiece

G3P2StateEndomorphismSurface :
  Set (lsuc lzero)
G3P2StateEndomorphismSurface =
  DMC.DASHIState →
  DMC.DASHIState

G3P2BumpFamilySurface :
  Set (lsuc lzero)
G3P2BumpFamilySurface =
  G3P2BumpKind →
  G3P2StateEndomorphismSurface

G3P2MomentumOperatorFamilySurface :
  Set (lsuc lzero)
G3P2MomentumOperatorFamilySurface =
  G3P2MomentumGenerator →
  G3P2StateEndomorphismSurface

G3P2BoostOperatorFamilySurface :
  Set (lsuc lzero)
G3P2BoostOperatorFamilySurface =
  G3P2BoostGenerator →
  G3P2StateEndomorphismSurface

G3P2NamedOperatorFamilySurface :
  Set (lsuc lzero)
G3P2NamedOperatorFamilySurface =
  G3P2NamedOperator →
  G3P2StateEndomorphismSurface

G3P2CommutatorObligationSurface :
  Set (lsuc lzero)
G3P2CommutatorObligationSurface =
  G3P2StateEndomorphismSurface →
  G3P2StateEndomorphismSurface →
  G3P2StateEndomorphismSurface →
  Set

G3P2FilteredOperatorLawSurface :
  Set (lsuc lzero)
G3P2FilteredOperatorLawSurface =
  G3.G3CarrierToFactorVecP2FiltrationSurface →
  G3P2StateEndomorphismSurface →
  Set

G3P2FilteredCommutatorLawSurface :
  Set (lsuc lzero)
G3P2FilteredCommutatorLawSurface =
  G3.G3CarrierToFactorVecP2FiltrationSurface →
  G3P2StateEndomorphismSurface →
  G3P2StateEndomorphismSurface →
  G3P2StateEndomorphismSurface →
  Set

adapterP2BumpState :
  G3.G3CarrierToFactorVecMinimalAdapter →
  G3P2StateEndomorphismSurface
adapterP2BumpState =
  G3.G3CarrierToFactorVecMinimalAdapter.p2PrimeBumpState

adapterP2Filtration :
  G3.G3CarrierToFactorVecMinimalAdapter →
  G3.G3CarrierToFactorVecP2FiltrationSurface
adapterP2Filtration =
  G3.G3CarrierToFactorVecMinimalAdapter.p2Filtration

adapterP2BumpFactorVecLaw :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3.G3CarrierToFactorVecP2BumpFactorVecLawSurface
    (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
    (adapterP2BumpState adapter)
adapterP2BumpFactorVecLaw =
  G3.G3CarrierToFactorVecMinimalAdapter.p2PrimeBumpFactorVecLaw

adapterP2BumpExponentLaw :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3.G3CarrierToFactorVecP2BumpExponentLawSurface
    (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
    (adapterP2BumpState adapter)
adapterP2BumpExponentLaw =
  G3.minimalAdapterP2BumpExponentLaw

adapterP2FiltrationTracksExponent :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3.G3CarrierToFactorVecP2FiltrationTracksExponentSurface
    (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
    (adapterP2Filtration adapter)
adapterP2FiltrationTracksExponent =
  G3.G3CarrierToFactorVecMinimalAdapter.p2FiltrationTracksExponent

record G3AdapterBackedPHKOperatorObligations
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) : Setω where
  field
    pOperatorSurface :
      Set (lsuc lzero)

    pOperatorSurfaceIsExact :
      pOperatorSurface ≡ G3P2StateEndomorphismSurface

    hOperatorSurface :
      Set (lsuc lzero)

    hOperatorSurfaceIsExact :
      hOperatorSurface ≡ G3P2StateEndomorphismSurface

    kOperatorSurface :
      Set (lsuc lzero)

    kOperatorSurfaceIsExact :
      kOperatorSurface ≡ G3P2StateEndomorphismSurface

    namedOperatorFamilySurface :
      Set (lsuc lzero)

    namedOperatorFamilySurfaceIsExact :
      namedOperatorFamilySurface ≡ G3P2NamedOperatorFamilySurface

    filteredOperatorLawSurface :
      Set (lsuc lzero)

    filteredOperatorLawSurfaceIsExact :
      filteredOperatorLawSurface ≡ G3P2FilteredOperatorLawSurface

    adapterFiltration :
      G3.G3CarrierToFactorVecP2FiltrationSurface

    adapterFiltrationIsExact :
      adapterFiltration ≡ adapterP2Filtration adapter

    adapterFiltrationTracksExponent :
      G3.G3CarrierToFactorVecP2FiltrationTracksExponentSurface
        (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
        adapterFiltration

    missingOperatorLaws :
      List G3P2OperatorMissingPiece

    nextMissingLaw :
      String

canonicalG3AdapterBackedPHKOperatorObligations :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3AdapterBackedPHKOperatorObligations adapter
canonicalG3AdapterBackedPHKOperatorObligations adapter =
  record
    { pOperatorSurface =
        G3P2StateEndomorphismSurface
    ; pOperatorSurfaceIsExact =
        refl
    ; hOperatorSurface =
        G3P2StateEndomorphismSurface
    ; hOperatorSurfaceIsExact =
        refl
    ; kOperatorSurface =
        G3P2StateEndomorphismSurface
    ; kOperatorSurfaceIsExact =
        refl
    ; namedOperatorFamilySurface =
        G3P2NamedOperatorFamilySurface
    ; namedOperatorFamilySurfaceIsExact =
        refl
    ; filteredOperatorLawSurface =
        G3P2FilteredOperatorLawSurface
    ; filteredOperatorLawSurfaceIsExact =
        refl
    ; adapterFiltration =
        adapterP2Filtration adapter
    ; adapterFiltrationIsExact =
        refl
    ; adapterFiltrationTracksExponent =
        adapterP2FiltrationTracksExponent adapter
    ; missingOperatorLaws =
        missingPActionLaw
        ∷ missingHActionLaw
        ∷ missingKActionLaw
        ∷ []
    ; nextMissingLaw =
        "P : G3P2StateEndomorphismSurface with a filtered adapter-p2 action law"
    }

record G3AdapterBackedCommutatorObligations
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) : Setω where
  field
    commutatorSurface :
      Set (lsuc lzero)

    commutatorSurfaceIsExact :
      commutatorSurface ≡ G3P2CommutatorObligationSurface

    filteredCommutatorLawSurface :
      Set (lsuc lzero)

    filteredCommutatorLawSurfaceIsExact :
      filteredCommutatorLawSurface ≡ G3P2FilteredCommutatorLawSurface

    filtration :
      G3.G3CarrierToFactorVecP2FiltrationSurface

    filtrationIsAdapterFiltration :
      filtration ≡ adapterP2Filtration adapter

    requiredBracketNames :
      List String

    missingCommutatorLaws :
      List G3P2OperatorMissingPiece

    nextMissingLaw :
      String

canonicalG3AdapterBackedCommutatorObligations :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3AdapterBackedCommutatorObligations adapter
canonicalG3AdapterBackedCommutatorObligations adapter =
  record
    { commutatorSurface =
        G3P2CommutatorObligationSurface
    ; commutatorSurfaceIsExact =
        refl
    ; filteredCommutatorLawSurface =
        G3P2FilteredCommutatorLawSurface
    ; filteredCommutatorLawSurfaceIsExact =
        refl
    ; filtration =
        adapterP2Filtration adapter
    ; filtrationIsAdapterFiltration =
        refl
    ; requiredBracketNames =
        "[P , P] adapter-filtered commutator obligation"
        ∷ "[P , H] adapter-filtered commutator obligation"
        ∷ "[K , H] adapter-filtered commutator obligation"
        ∷ "[P , K] adapter-filtered commutator obligation"
        ∷ "[K , K] adapter-filtered commutator obligation"
        ∷ []
    ; missingCommutatorLaws =
        missingPPCommutatorLaw
        ∷ missingPHCommutatorLaw
        ∷ missingKHCommutatorLaw
        ∷ missingPKCommutatorLaw
        ∷ missingKKCommutatorLaw
        ∷ missingFilteredCommutatorCompatibility
        ∷ []
    ; nextMissingLaw =
        "commutator : P/H/K actions must close and respect adapterP2Filtration"
    }

record G3AdapterBackedIWContractionRequest
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) : Setω where
  field
    filtration :
      G3.G3CarrierToFactorVecP2FiltrationSurface

    filtrationIsAdapterFiltration :
      filtration ≡ adapterP2Filtration adapter

    filtrationTracksExponent :
      G3.G3CarrierToFactorVecP2FiltrationTracksExponentSurface
        (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
        filtration

    requiredPHKOperatorObligations :
      G3AdapterBackedPHKOperatorObligations adapter

    requiredCommutatorObligations :
      G3AdapterBackedCommutatorObligations adapter

    requestedAssociatedGradedCarrier :
      String

    requestedContractionParameterLaw :
      String

    requestedGalileiIdentificationLaw :
      String

    statusBoundary :
      List String

canonicalG3AdapterBackedIWContractionRequest :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3AdapterBackedIWContractionRequest adapter
canonicalG3AdapterBackedIWContractionRequest adapter =
  record
    { filtration =
        adapterP2Filtration adapter
    ; filtrationIsAdapterFiltration =
        refl
    ; filtrationTracksExponent =
        adapterP2FiltrationTracksExponent adapter
    ; requiredPHKOperatorObligations =
        canonicalG3AdapterBackedPHKOperatorObligations adapter
    ; requiredCommutatorObligations =
        canonicalG3AdapterBackedCommutatorObligations adapter
    ; requestedAssociatedGradedCarrier =
        "associated graded carrier for P/H/K over adapterP2Filtration"
    ; requestedContractionParameterLaw =
        "IW contraction parameter law compatible with the adapter p2 exponent"
    ; requestedGalileiIdentificationLaw =
        "Galilei-sector identification of the associated graded P/H/K commutator package"
    ; statusBoundary =
        "IW request only: the adapter supplies p2 filtration, not an associated graded carrier"
        ∷ "No PoincareToGalileiContractionCarrier inhabitant is constructed"
        ∷ "Promotion requires inhabited P/H/K actions, filtered commutators, contraction parameter law, and Galilei identification"
        ∷ []
    }

record G3P2OperatorSurface
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) : Setω where
  field
    status :
      G3P2OperatorSurfaceStatus

    p2BumpState :
      G3P2StateEndomorphismSurface

    p2BumpStateIsAdapterBump :
      p2BumpState ≡ adapterP2BumpState adapter

    p2BumpFactorVecLaw :
      G3.G3CarrierToFactorVecP2BumpFactorVecLawSurface
        (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
        p2BumpState

    p2BumpExponentLaw :
      G3.G3CarrierToFactorVecP2BumpExponentLawSurface
        (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
        p2BumpState

    p2Filtration :
      G3.G3CarrierToFactorVecP2FiltrationSurface

    p2FiltrationIsAdapterFiltration :
      p2Filtration ≡ adapterP2Filtration adapter

    p2FiltrationTracksExponent :
      G3.G3CarrierToFactorVecP2FiltrationTracksExponentSurface
        (G3.G3CarrierToFactorVecMinimalAdapter.factorVec adapter)
        p2Filtration

    p2ExponentAccessor :
      DMC.DASHIState →
      Nat

    p2ExponentAccessorIsFactorVecProjection :
      p2ExponentAccessor
      ≡
      (λ σ →
        GL.Vec15.e2
          (G3.G3CarrierToFactorVecMinimalAdapter.factorVec
            adapter
            σ
            (G3.dashiStateCarrierValue σ)))

    bumpFamilySurface :
      Set (lsuc lzero)

    bumpFamilySurfaceIsExact :
      bumpFamilySurface ≡ G3P2BumpFamilySurface

    spatialBumpStateSurface :
      Set (lsuc lzero)

    spatialBumpStateSurfaceIsExact :
      spatialBumpStateSurface ≡ G3P2StateEndomorphismSurface

    momentumOperatorSurface :
      Set (lsuc lzero)

    momentumOperatorSurfaceIsExact :
      momentumOperatorSurface ≡ G3P2MomentumOperatorFamilySurface

    boostOperatorSurface :
      Set (lsuc lzero)

    boostOperatorSurfaceIsExact :
      boostOperatorSurface ≡ G3P2BoostOperatorFamilySurface

    namedPHKOperatorSurface :
      Set (lsuc lzero)

    namedPHKOperatorSurfaceIsExact :
      namedPHKOperatorSurface ≡ G3P2NamedOperatorFamilySurface

    commutatorObligationSurface :
      Set (lsuc lzero)

    commutatorObligationSurfaceIsExact :
      commutatorObligationSurface ≡ G3P2CommutatorObligationSurface

    phkOperatorObligations :
      G3AdapterBackedPHKOperatorObligations adapter

    adapterBackedCommutatorObligations :
      G3AdapterBackedCommutatorObligations adapter

    iwContractionRequest :
      G3AdapterBackedIWContractionRequest adapter

    requiredCommutatorObligationNames :
      List String

    missingPieces :
      List G3P2OperatorMissingPiece

    nonPromotionBoundary :
      List String

canonicalG3P2OperatorSurface :
  (adapter : G3.G3CarrierToFactorVecMinimalAdapter) →
  G3P2OperatorSurface adapter
canonicalG3P2OperatorSurface adapter =
  record
    { status =
        conditionalP2OperatorSurfaceOnlyNoPromotion
    ; p2BumpState =
        adapterP2BumpState adapter
    ; p2BumpStateIsAdapterBump =
        refl
    ; p2BumpFactorVecLaw =
        adapterP2BumpFactorVecLaw adapter
    ; p2BumpExponentLaw =
        adapterP2BumpExponentLaw adapter
    ; p2Filtration =
        adapterP2Filtration adapter
    ; p2FiltrationIsAdapterFiltration =
        refl
    ; p2FiltrationTracksExponent =
        adapterP2FiltrationTracksExponent adapter
    ; p2ExponentAccessor =
        λ σ →
          GL.Vec15.e2
            (G3.G3CarrierToFactorVecMinimalAdapter.factorVec
              adapter
              σ
              (G3.dashiStateCarrierValue σ))
    ; p2ExponentAccessorIsFactorVecProjection =
        refl
    ; bumpFamilySurface =
        G3P2BumpFamilySurface
    ; bumpFamilySurfaceIsExact =
        refl
    ; spatialBumpStateSurface =
        G3P2StateEndomorphismSurface
    ; spatialBumpStateSurfaceIsExact =
        refl
    ; momentumOperatorSurface =
        G3P2MomentumOperatorFamilySurface
    ; momentumOperatorSurfaceIsExact =
        refl
    ; boostOperatorSurface =
        G3P2BoostOperatorFamilySurface
    ; boostOperatorSurfaceIsExact =
        refl
    ; namedPHKOperatorSurface =
        G3P2NamedOperatorFamilySurface
    ; namedPHKOperatorSurfaceIsExact =
        refl
    ; commutatorObligationSurface =
        G3P2CommutatorObligationSurface
    ; commutatorObligationSurfaceIsExact =
        refl
    ; phkOperatorObligations =
        canonicalG3AdapterBackedPHKOperatorObligations adapter
    ; adapterBackedCommutatorObligations =
        canonicalG3AdapterBackedCommutatorObligations adapter
    ; iwContractionRequest =
        canonicalG3AdapterBackedIWContractionRequest adapter
    ; requiredCommutatorObligationNames =
        "[P , P] closes on the selected p2/spatial operator family"
        ∷ "[P , H] closes on the selected p2/spatial operator family"
        ∷ "[K , H] closes on the selected p2/spatial operator family"
        ∷ "[P , K] closes on the selected p2/spatial operator family"
        ∷ "[K , K] closes on the selected p2/spatial operator family"
        ∷ "commutator obligations must target the same adapter-indexed p2 filtration"
        ∷ []
    ; missingPieces =
        missingSpatialBumpState
        ∷ missingPActionLaw
        ∷ missingHActionLaw
        ∷ missingKActionLaw
        ∷ missingPPCommutatorLaw
        ∷ missingPHCommutatorLaw
        ∷ missingKHCommutatorLaw
        ∷ missingPKCommutatorLaw
        ∷ missingKKCommutatorLaw
        ∷ missingFilteredCommutatorCompatibility
        ∷ missingIWContractionParameterLaw
        ∷ missingPoincareAtP2PromotionWitness
        ∷ []
    ; nonPromotionBoundary =
        "This package is conditional on an external G3CarrierToFactorVecMinimalAdapter; no adapter is constructed here"
        ∷ "The p2 bump and p2 filtration are exactly the adapter-provided operations and laws"
        ∷ "P, H, K, spatial bump, commutator, and IW contraction laws are typed obligation surfaces only"
        ∷ "No PoincareSectorCarrier, IW associated graded carrier, or G3/IW closure inhabitant is claimed"
        ∷ []
    }
