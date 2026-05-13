module DASHI.Physics.Closure.G3SelectedCarrierInstance where

open import Agda.Primitive using (Set; Setω; lzero; lsuc)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)

import DASHI.Process.DASHIMarkovCompatibility as DMC
import DASHI.Physics.Closure.G3PoincareGalileiCarrierChain as G3
open import MonsterOntos using (p2)
import Ontology.GodelLattice as GL
import Ontology.Hecke.FactorVecInstances as FVI

------------------------------------------------------------------------
-- Selected G3 carrier instance.
--
-- This module constructs a concrete selected DASHIState whose carrier is
-- exactly FactorVec.  It proves the p2 bump/projection laws for that selected
-- state surface only.  It deliberately does not inhabit the global
-- G3CarrierToFactorVecMinimalAdapter, because that adapter quantifies over
-- every DMC.DASHIState and arbitrary Carrier fields.

selectedZeroFactorVec : GL.FactorVec
selectedZeroFactorVec =
  GL.v15
    zero zero zero zero zero
    zero zero zero zero zero
    zero zero zero zero zero

data G3SelectedCarrierResidual : Set where
  selectedCarrierOnlyNoGlobalAdapter :
    G3SelectedCarrierResidual

data G3SelectedCarrierObligation : Set where
  selectedCarrierFactorVecProjectionOnly :
    G3SelectedCarrierObligation

data G3SelectedCarrierAuthority : Set where
  selectedCarrierLocalAuthorityOnly :
    G3SelectedCarrierAuthority

data G3SelectedCarrierBoundary : Set where
  selectedCarrierNoG3Closure :
    G3SelectedCarrierBoundary

data G3SelectedCarrierPromotionStatus : Set where
  selectedCarrierInstanceOnlyNoPromotion :
    G3SelectedCarrierPromotionStatus

selectedG3FactorVecDASHIState :
  DMC.DASHIState
selectedG3FactorVecDASHIState =
  record
    { Carrier =
        GL.FactorVec
    ; carrierValue =
        selectedZeroFactorVec
    ; ResidualSurface =
        G3SelectedCarrierResidual
    ; residualValue =
        selectedCarrierOnlyNoGlobalAdapter
    ; ObligationSurface =
        G3SelectedCarrierObligation
    ; obligations =
        selectedCarrierFactorVecProjectionOnly
    ; AuthoritySurface =
        G3SelectedCarrierAuthority
    ; authorities =
        selectedCarrierLocalAuthorityOnly
    ; BoundarySurface =
        G3SelectedCarrierBoundary
    ; boundary =
        selectedCarrierNoG3Closure
    ; PromotionSurface =
        G3SelectedCarrierPromotionStatus
    ; promotionStatus =
        selectedCarrierInstanceOnlyNoPromotion
    }

selectedG3P2BumpedDASHIState :
  DMC.DASHIState
selectedG3P2BumpedDASHIState =
  record
    { Carrier =
        GL.FactorVec
    ; carrierValue =
        FVI.primeBump p2 selectedZeroFactorVec
    ; ResidualSurface =
        G3SelectedCarrierResidual
    ; residualValue =
        selectedCarrierOnlyNoGlobalAdapter
    ; ObligationSurface =
        G3SelectedCarrierObligation
    ; obligations =
        selectedCarrierFactorVecProjectionOnly
    ; AuthoritySurface =
        G3SelectedCarrierAuthority
    ; authorities =
        selectedCarrierLocalAuthorityOnly
    ; BoundarySurface =
        G3SelectedCarrierBoundary
    ; boundary =
        selectedCarrierNoG3Closure
    ; PromotionSurface =
        G3SelectedCarrierPromotionStatus
    ; promotionStatus =
        selectedCarrierInstanceOnlyNoPromotion
    }

selectedCarrierIsFactorVec :
  DMC.DASHIState.Carrier selectedG3FactorVecDASHIState
  ≡
  GL.FactorVec
selectedCarrierIsFactorVec =
  refl

selectedBumpedCarrierIsFactorVec :
  DMC.DASHIState.Carrier selectedG3P2BumpedDASHIState
  ≡
  GL.FactorVec
selectedBumpedCarrierIsFactorVec =
  refl

selectedCarrierFactorVec :
  DMC.DASHIState.Carrier selectedG3FactorVecDASHIState →
  GL.FactorVec
selectedCarrierFactorVec x =
  x

selectedBumpedCarrierFactorVec :
  DMC.DASHIState.Carrier selectedG3P2BumpedDASHIState →
  GL.FactorVec
selectedBumpedCarrierFactorVec x =
  x

selectedCarrierValueFactorVec :
  selectedCarrierFactorVec
    (DMC.DASHIState.carrierValue selectedG3FactorVecDASHIState)
  ≡
  selectedZeroFactorVec
selectedCarrierValueFactorVec =
  refl

selectedP2BumpedCarrierValueFactorVec :
  selectedBumpedCarrierFactorVec
    (DMC.DASHIState.carrierValue selectedG3P2BumpedDASHIState)
  ≡
  FVI.primeBump p2
    (selectedCarrierFactorVec
      (DMC.DASHIState.carrierValue selectedG3FactorVecDASHIState))
selectedP2BumpedCarrierValueFactorVec =
  refl

selectedP2Exponent :
  Nat
selectedP2Exponent =
  GL.Vec15.e2
    (selectedCarrierFactorVec
      (DMC.DASHIState.carrierValue selectedG3FactorVecDASHIState))

selectedP2BumpedExponent :
  Nat
selectedP2BumpedExponent =
  GL.Vec15.e2
    (selectedBumpedCarrierFactorVec
      (DMC.DASHIState.carrierValue selectedG3P2BumpedDASHIState))

selectedP2BumpExponentLaw :
  selectedP2BumpedExponent
  ≡
  suc selectedP2Exponent
selectedP2BumpExponentLaw =
  trans
    (refl
      {x =
        GL.Vec15.e2
          (FVI.primeBump p2 selectedZeroFactorVec)})
    (G3.p2ExponentAfterPrimeBump selectedZeroFactorVec)

selectedP2Filtration :
  DMC.DASHIState →
  Nat
selectedP2Filtration σ =
  GL.Vec15.e2
    (selectedCarrierFactorVec
      (DMC.DASHIState.carrierValue selectedG3FactorVecDASHIState))

selectedP2FiltrationTracksExponent :
  selectedP2Filtration selectedG3FactorVecDASHIState
  ≡
  selectedP2Exponent
selectedP2FiltrationTracksExponent =
  refl

data G3SelectedCarrierInstanceStatus : Set where
  selectedFactorVecCarrierInstanceNoGlobalPromotion :
    G3SelectedCarrierInstanceStatus

record G3SelectedCarrierFactorVecAdapter : Setω where
  field
    status :
      G3SelectedCarrierInstanceStatus

    selectedState :
      DMC.DASHIState

    selectedStateIsFactorVecCarrier :
      DMC.DASHIState.Carrier selectedState
      ≡
      GL.FactorVec

    selectedStateValue :
      DMC.DASHIState.Carrier selectedState

    selectedStateValueIsCarrierValue :
      selectedStateValue
      ≡
      DMC.DASHIState.carrierValue selectedState

    factorVec :
      DMC.DASHIState.Carrier selectedState →
      GL.FactorVec

    factorVecCarrierValueLaw :
      factorVec (DMC.DASHIState.carrierValue selectedState)
      ≡
      selectedZeroFactorVec

    p2BumpedState :
      DMC.DASHIState

    p2BumpedStateIsFactorVecCarrier :
      DMC.DASHIState.Carrier p2BumpedState
      ≡
      GL.FactorVec

    p2BumpedFactorVec :
      DMC.DASHIState.Carrier p2BumpedState →
      GL.FactorVec

    p2BumpFactorVecLaw :
      p2BumpedFactorVec (DMC.DASHIState.carrierValue p2BumpedState)
      ≡
      FVI.primeBump p2
        (factorVec (DMC.DASHIState.carrierValue selectedState))

    p2BumpExponentLaw :
      GL.Vec15.e2
        (p2BumpedFactorVec (DMC.DASHIState.carrierValue p2BumpedState))
      ≡
      suc
        (GL.Vec15.e2
          (factorVec (DMC.DASHIState.carrierValue selectedState)))

    nonPromotionBoundary :
      List String

canonicalG3SelectedCarrierFactorVecAdapter :
  G3SelectedCarrierFactorVecAdapter
canonicalG3SelectedCarrierFactorVecAdapter =
  record
    { status =
        selectedFactorVecCarrierInstanceNoGlobalPromotion
    ; selectedState =
        selectedG3FactorVecDASHIState
    ; selectedStateIsFactorVecCarrier =
        refl
    ; selectedStateValue =
        DMC.DASHIState.carrierValue selectedG3FactorVecDASHIState
    ; selectedStateValueIsCarrierValue =
        refl
    ; factorVec =
        selectedCarrierFactorVec
    ; factorVecCarrierValueLaw =
        selectedCarrierValueFactorVec
    ; p2BumpedState =
        selectedG3P2BumpedDASHIState
    ; p2BumpedStateIsFactorVecCarrier =
        refl
    ; p2BumpedFactorVec =
        selectedBumpedCarrierFactorVec
    ; p2BumpFactorVecLaw =
        selectedP2BumpedCarrierValueFactorVec
    ; p2BumpExponentLaw =
        selectedP2BumpExponentLaw
    ; nonPromotionBoundary =
        "This is a selected DASHIState instance whose Carrier is definitionally GL.FactorVec"
        ∷ "It proves the selected-state carrier projection and p2 bump/exponent law only for selectedG3FactorVecDASHIState"
        ∷ "It is not a G3CarrierToFactorVecMinimalAdapter because that adapter requires factorVec for every DMC.DASHIState.Carrier"
        ∷ "No PoincareSectorCarrier, IW associated graded carrier, or G3 closure theorem is inhabited here"
        ∷ []
    }

data G3SelectedCarrierGlobalAdapterGap : Set where
  missingGlobalDASHIStateCarrierSpecialization :
    G3SelectedCarrierGlobalAdapterGap

record G3SelectedCarrierGlobalAdapterRequest : Setω where
  field
    selectedInstance :
      G3SelectedCarrierFactorVecAdapter

    requestedGlobalAdapter :
      String

    exactBlockingField :
      String

    exactBlockingLaw :
      String

    requiredConstructorOrSpecializer :
      String

    gap :
      G3SelectedCarrierGlobalAdapterGap

canonicalG3SelectedCarrierGlobalAdapterRequest :
  G3SelectedCarrierGlobalAdapterRequest
canonicalG3SelectedCarrierGlobalAdapterRequest =
  record
    { selectedInstance =
        canonicalG3SelectedCarrierFactorVecAdapter
    ; requestedGlobalAdapter =
        "G3CarrierToFactorVecMinimalAdapter"
    ; exactBlockingField =
        "factorVec : (σ : DMC.DASHIState) -> DMC.DASHIState.Carrier σ -> GL.FactorVec"
    ; exactBlockingLaw =
        "p2PrimeBumpFactorVecLaw : factorVec (p2PrimeBumpState σ) (DMC.DASHIState.carrierValue (p2PrimeBumpState σ)) == FVI.primeBump p2 (factorVec σ (DMC.DASHIState.carrierValue σ))"
    ; requiredConstructorOrSpecializer =
        "Either a DMC.DASHIState constructor/specializer restricting σ to selectedG3FactorVecDASHIState, or a real global projection law for every DASHIState.Carrier"
    ; gap =
        missingGlobalDASHIStateCarrierSpecialization
    }
