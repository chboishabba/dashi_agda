module DASHI.Physics.Closure.UltrametricAubinLionsCompactness where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Core.AuthorityBoundary as Authority
import DASHI.Physics.Closure.AubinLionsBound3Full as Bound3Full
import DASHI.Physics.Closure.UltrametricAubinLionsReceipt as UAL

------------------------------------------------------------------------
-- Ultrametric Aubin-Lions compactness receipt.
--
-- This is the compactness step after the three-bound route is assembled.  It
-- records Aubin-Lions as a citation authority and identifies the exact
-- precompact subsequence target.  It remains fail-closed: no smooth
-- continuum NS solution or Clay promotion is constructed here.

data UltrametricCompactnessInput : Set where
  l2TimeH1Bound :
    UltrametricCompactnessInput

  l2TimeHMinusOneTimeDerivativeBound :
    UltrametricCompactnessInput

  ultrametricSobolevUniformEmbedding :
    UltrametricCompactnessInput

canonicalUltrametricCompactnessInputs :
  List UltrametricCompactnessInput
canonicalUltrametricCompactnessInputs =
  l2TimeH1Bound
  ∷ l2TimeHMinusOneTimeDerivativeBound
  ∷ ultrametricSobolevUniformEmbedding
  ∷ []

data UltrametricAubinLionsCompactnessTarget : Set where
  precompactSubsequenceInL2TimeL2Space :
    UltrametricAubinLionsCompactnessTarget

data UltrametricAubinLionsCompactnessBlocker : Set where
  missingCarrierSpecializedAubinLionsProof :
    UltrametricAubinLionsCompactnessBlocker

  missingBound3FullEstimateConstruction :
    UltrametricAubinLionsCompactnessBlocker

  missingLimitEquationPassage :
    UltrametricAubinLionsCompactnessBlocker

canonicalUltrametricAubinLionsCompactnessBlockers :
  List UltrametricAubinLionsCompactnessBlocker
canonicalUltrametricAubinLionsCompactnessBlockers =
  missingCarrierSpecializedAubinLionsProof
  ∷ missingBound3FullEstimateConstruction
  ∷ missingLimitEquationPassage
  ∷ []

aubinLionsCitation :
  Authority.CitationAuthorityBoundary
aubinLionsCitation =
  Authority.mkAuthorityBoundary
    Authority.CitationAuthority
    refl
    "Aubin-Lions compactness lemma"
    "J.-L. Lions, Quelques methodes de resolution des problemes aux limites non lineaires; carrier ultrametric specialization recorded as an authority boundary"
    true
    false
    false
    ( "CitationAuthority only"
      ∷ "No machine-readable artifact is required for this standard compactness lemma"
      ∷ "The DASHI carrier specialization remains a proof obligation"
      ∷ []
    )

aubinLionsNoArtifact :
  Authority.CitationAuthorityNoArtifact
aubinLionsNoArtifact =
  Authority.mkCitationAuthorityNoArtifact
    aubinLionsCitation
    refl
    refl
    refl

record UltrametricAubinLionsCompactnessReceipt : Setω where
  field
    ultrametricAubinLionsReceipt :
      UAL.UltrametricAubinLionsReceipt

    bound3FullReceipt :
      Bound3Full.AubinLionsBound3FullReceipt

    bound3FullEstimateConstructed :
      Bound3Full.fullBound3EstimateConstructedHere bound3FullReceipt
      ≡
      true

    compactnessInputs :
      List UltrametricCompactnessInput

    compactnessInputsAreCanonical :
      compactnessInputs ≡ canonicalUltrametricCompactnessInputs

    compactnessTarget :
      UltrametricAubinLionsCompactnessTarget

    compactnessTargetIsCanonical :
      compactnessTarget ≡ precompactSubsequenceInL2TimeL2Space

    aubinLionsAuthorityBoundary :
      Authority.CitationAuthorityBoundary

    aubinLionsAuthorityNoArtifact :
      Authority.CitationAuthorityNoArtifact

    aubinLionsAuthorityAccepted :
      Authority.authorityAccepted aubinLionsAuthorityBoundary ≡ true

    carrierSpecializedCompactnessConstructed :
      Bool

    carrierSpecializedCompactnessConstructedIsFalse :
      carrierSpecializedCompactnessConstructed ≡ false

    precompactSubsequenceConstructed :
      Bool

    precompactSubsequenceConstructedIsFalse :
      precompactSubsequenceConstructed ≡ false

    smoothLimitConstructed :
      Bool

    smoothLimitConstructedIsFalse :
      smoothLimitConstructed ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    blockers :
      List UltrametricAubinLionsCompactnessBlocker

    blockersAreCanonical :
      blockers ≡ canonicalUltrametricAubinLionsCompactnessBlockers

    receiptBoundary :
      List String

open UltrametricAubinLionsCompactnessReceipt public

canonicalUltrametricAubinLionsCompactnessReceipt :
  UltrametricAubinLionsCompactnessReceipt
canonicalUltrametricAubinLionsCompactnessReceipt =
  record
    { ultrametricAubinLionsReceipt =
        UAL.canonicalUltrametricAubinLionsReceipt
    ; bound3FullReceipt =
        Bound3Full.canonicalAubinLionsBound3FullReceipt
    ; bound3FullEstimateConstructed =
        refl
    ; compactnessInputs =
        canonicalUltrametricCompactnessInputs
    ; compactnessInputsAreCanonical =
        refl
    ; compactnessTarget =
        precompactSubsequenceInL2TimeL2Space
    ; compactnessTargetIsCanonical =
        refl
    ; aubinLionsAuthorityBoundary =
        aubinLionsCitation
    ; aubinLionsAuthorityNoArtifact =
        aubinLionsNoArtifact
    ; aubinLionsAuthorityAccepted =
        refl
    ; carrierSpecializedCompactnessConstructed =
        false
    ; carrierSpecializedCompactnessConstructedIsFalse =
        refl
    ; precompactSubsequenceConstructed =
        false
    ; precompactSubsequenceConstructedIsFalse =
        refl
    ; smoothLimitConstructed =
        false
    ; smoothLimitConstructedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blockers =
        canonicalUltrametricAubinLionsCompactnessBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Aubin-Lions is consumed as CitationAuthority for the compactness shape"
        ∷ "The target is precompact subsequence extraction in L2([0,T];L2)"
        ∷ "The weak time-derivative Bound 3 receipt is available, but the carrier-specialized ultrametric compactness lemma is still not constructed"
        ∷ "Smooth convergence and Clay Navier-Stokes promotion remain false"
        ∷ []
    }

ultrametricAubinLionsCompactnessAuthorityAccepted :
  Authority.authorityAccepted
    (aubinLionsAuthorityBoundary
      canonicalUltrametricAubinLionsCompactnessReceipt)
  ≡
  true
ultrametricAubinLionsCompactnessAuthorityAccepted =
  refl

ultrametricAubinLionsCompactnessStillOpen :
  carrierSpecializedCompactnessConstructed
    canonicalUltrametricAubinLionsCompactnessReceipt
  ≡
  false
ultrametricAubinLionsCompactnessStillOpen =
  refl

ultrametricAubinLionsCompactnessDoesNotPromoteClay :
  clayNavierStokesPromoted canonicalUltrametricAubinLionsCompactnessReceipt
  ≡
  false
ultrametricAubinLionsCompactnessDoesNotPromoteClay =
  refl
