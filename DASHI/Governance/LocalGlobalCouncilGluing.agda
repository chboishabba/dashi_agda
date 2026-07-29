module DASHI.Governance.LocalGlobalCouncilGluing where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.StageValuationBundleAtlas as Stage

------------------------------------------------------------------------
-- Local/global council gluing.
--
-- The Charter's local -> locality -> state -> national assembly is related to
-- the existing BundleSheaf carrier.  Local sections do not become one global
-- section merely by coexisting: a compatibility witness is carried into the
-- gluing operation, and gluing must restrict back to every local section.
--
-- This is a finite structural analogy, not a claim of mathematical sheaf
-- semantics for real political communities and not a source of authority.
------------------------------------------------------------------------

data CouncilBasePoint : Set where
  neighbourhoodPoint : CouncilBasePoint
  ruralLocalityPoint : CouncilBasePoint
  electedUnionPoint : CouncilBasePoint
  idpCampPoint : CouncilBasePoint

record LocalCouncilSection : Set where
  constructor localCouncilSection
  field
    sectionLabel : String
    representedConstituency : String
    mandateValid : Bool
    mandateValidIsTrue : mandateValid ≡ true
    recallAvailable : Bool
    recallAvailableIsTrue : recallAvailable ≡ true

open LocalCouncilSection public

mkLocalCouncilSection : String → String → LocalCouncilSection
mkLocalCouncilSection label constituency =
  localCouncilSection
    label
    constituency
    true
    refl
    true
    refl

record GlobalCouncilSection : Set where
  constructor globalCouncilSection
  field
    sectionAt : CouncilBasePoint → LocalCouncilSection

open GlobalCouncilSection public

record CompatibleCouncilFamily
  (locals : CouncilBasePoint → LocalCouncilSection) : Set where
  constructor compatibleCouncilFamily
  field
    neighbourhoodMandateValid :
      mandateValid (locals neighbourhoodPoint) ≡ true
    ruralMandateValid :
      mandateValid (locals ruralLocalityPoint) ≡ true
    unionMandateValid :
      mandateValid (locals electedUnionPoint) ≡ true
    idpMandateValid :
      mandateValid (locals idpCampPoint) ≡ true
    neighbourhoodRecallAvailable :
      recallAvailable (locals neighbourhoodPoint) ≡ true
    ruralRecallAvailable :
      recallAvailable (locals ruralLocalityPoint) ≡ true
    unionRecallAvailable :
      recallAvailable (locals electedUnionPoint) ≡ true
    idpRecallAvailable :
      recallAvailable (locals idpCampPoint) ≡ true

open CompatibleCouncilFamily public

canonicalLocalCouncilFamily : CouncilBasePoint → LocalCouncilSection
canonicalLocalCouncilFamily neighbourhoodPoint =
  mkLocalCouncilSection
    "neighbourhood section"
    "neighbourhood constituency"
canonicalLocalCouncilFamily ruralLocalityPoint =
  mkLocalCouncilSection
    "rural locality section"
    "rural constituency"
canonicalLocalCouncilFamily electedUnionPoint =
  mkLocalCouncilSection
    "elected union section"
    "workplace / functional constituency"
canonicalLocalCouncilFamily idpCampPoint =
  mkLocalCouncilSection
    "IDP camp section"
    "displaced-person constituency"

canonicalCouncilCompatibility :
  CompatibleCouncilFamily canonicalLocalCouncilFamily
canonicalCouncilCompatibility =
  compatibleCouncilFamily
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

rceppCouncilBundleSheaf :
  Stage.BundleSheaf
    CouncilBasePoint
    LocalCouncilSection
    GlobalCouncilSection
rceppCouncilBundleSheaf =
  record
    { restrict = λ global point → sectionAt global point
    ; compatible = CompatibleCouncilFamily
    ; glue = λ locals witness → globalCouncilSection locals
    ; glueRestricts = λ locals witness point → refl
    }

canonicalGlobalCouncilSection : GlobalCouncilSection
canonicalGlobalCouncilSection =
  Stage.BundleSheaf.glue
    rceppCouncilBundleSheaf
    canonicalLocalCouncilFamily
    canonicalCouncilCompatibility

canonicalGlobalRestrictsToNeighbourhood :
  Stage.BundleSheaf.restrict
    rceppCouncilBundleSheaf
    canonicalGlobalCouncilSection
    neighbourhoodPoint
  ≡ canonicalLocalCouncilFamily neighbourhoodPoint
canonicalGlobalRestrictsToNeighbourhood =
  Stage.BundleSheaf.glueRestricts
    rceppCouncilBundleSheaf
    canonicalLocalCouncilFamily
    canonicalCouncilCompatibility
    neighbourhoodPoint

canonicalGlobalRestrictsToIDPCamp :
  Stage.BundleSheaf.restrict
    rceppCouncilBundleSheaf
    canonicalGlobalCouncilSection
    idpCampPoint
  ≡ canonicalLocalCouncilFamily idpCampPoint
canonicalGlobalRestrictsToIDPCamp =
  Stage.BundleSheaf.glueRestricts
    rceppCouncilBundleSheaf
    canonicalLocalCouncilFamily
    canonicalCouncilCompatibility
    idpCampPoint

record CouncilGluingBoundary : Set where
  constructor councilGluingBoundary
  field
    localSectionsRemainExplicit : Bool
    compatibilityWitnessRequired : Bool
    globalRestrictsToLocals : Bool
    coexistenceAloneCreatesGlobalCouncil : Bool
    gluingErasesRecall : Bool
    sheafAnalogyCreatesPoliticalAuthority : Bool
    actualConstituencyCompatibilityEstablished : Bool

canonicalCouncilGluingBoundary : CouncilGluingBoundary
canonicalCouncilGluingBoundary =
  councilGluingBoundary
    true
    true
    true
    false
    false
    false
    false

canonicalLocalGlobalCouncilGluingReceipt :
  GenericReceipt.GenericReceipt
canonicalLocalGlobalCouncilGluingReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "proof-carrying local-global council gluing"
    "DASHI.Governance.LocalGlobalCouncilGluing"
    "rceppCouncilBundleSheaf"
    "instantiates the existing BundleSheaf carrier so compatible local mandate/recall sections glue into a global section that restricts back exactly to every local section"
    "the finite compatibility witness is internal to the model and does not establish actual political compatibility, apportionment, consent or authority"
    "agda -i . DASHI/Governance/LocalGlobalCouncilGluing.agda"
