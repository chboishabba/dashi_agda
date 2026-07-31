module DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-exact Osterwalder--Schrader positivity surface for the Wilson action.
--
-- P. Menotti and A. Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- Menotti--Pelissetto extend the Osterwalder--Seiler functional-integral proof
-- from reflections through planes cutting temporal links to reflections through
-- planes containing sites.  For the Wilson action this yields
--
--   < theta(F) F > >= 0
--
-- for every gauge-invariant observable F and for both parity classes of
-- Euclidean time separation.  In the Wilson-fermion case their site-plane proof
-- uses positivity of the boundary matrix B under K < 1/6.  They then record the
-- standard transfer-matrix conclusion 0 <= T <= 1.
--
-- This module imports that published theorem at its exact logical boundary.  It
-- does not claim that an arbitrary gauge-fixed or RG-effective action preserves
-- reflection positivity.  The repository-specific identification with the
-- literal Wilson measure and positive-time observable algebra remains explicit.
------------------------------------------------------------------------

record MenottiPelissettoSourceReceipt : Set where
  constructor menottiPelissettoSourceReceipt
  field
    firstAuthor : String
    secondAuthor : String
    title : String
    journal : String
    yearPages : String
    doi : String

open MenottiPelissettoSourceReceipt public

menottiPelissetto1987 : MenottiPelissettoSourceReceipt
menottiPelissetto1987 = record
  { firstAuthor = "P. Menotti"
  ; secondAuthor = "A. Pelissetto"
  ; title = "General Proof of Osterwalder-Schrader Positivity for the Wilson Action"
  ; journal = "Communications in Mathematical Physics 113"
  ; yearPages = "1987, 369-373"
  ; doi = "10.1007/BF01221251"
  }

data SeparationParity : Set where
  oddLinkPlane : SeparationParity
  evenSitePlane : SeparationParity

record WilsonReflectionPositivityData
    (Observable Scalar : Set) : Set₁ where
  field
    theta : Observable → Observable
    reflectedProductExpectation : Observable → Scalar

    GaugeInvariant PositiveTimeObservable : Observable → Set
    Nonnegative : Scalar → Set

    linkPlanePositivity : ∀ observable →
      GaugeInvariant observable →
      PositiveTimeObservable observable →
      Nonnegative (reflectedProductExpectation observable)

    sitePlanePositivity : ∀ observable →
      GaugeInvariant observable →
      PositiveTimeObservable observable →
      Nonnegative (reflectedProductExpectation observable)

    thetaAntilinearMeaning : Set
    wilsonActionMeasureMeaning : Set

    FermionsPresent : Set
    hoppingParameterBoundMeaning : FermionsPresent → Set

open WilsonReflectionPositivityData public

wilsonPositivityAtAnySeparationParity :
  ∀ {Observable Scalar}
    (dataSet : WilsonReflectionPositivityData Observable Scalar)
    parity observable →
  GaugeInvariant dataSet observable →
  PositiveTimeObservable dataSet observable →
  Nonnegative dataSet
    (reflectedProductExpectation dataSet observable)
wilsonPositivityAtAnySeparationParity dataSet oddLinkPlane observable =
  linkPlanePositivity dataSet observable
wilsonPositivityAtAnySeparationParity dataSet evenSitePlane observable =
  sitePlanePositivity dataSet observable

record TransferMatrixOrderData
    (Transfer Scalar : Set) : Set₁ where
  field
    transferMatrix : Transfer
    zero one : Scalar
    lowerValue upperValue : Transfer → Scalar
    LessEqual : Scalar → Scalar → Set

    lowerValueIsZero : lowerValue transferMatrix ≡ zero
    upperValueIsOne : upperValue transferMatrix ≡ one

    reflectionPositivityImpliesLowerBound :
      LessEqual (lowerValue transferMatrix) zero →
      LessEqual zero (lowerValue transferMatrix)

    wilsonNormalizationImpliesUpperBound :
      LessEqual one (upperValue transferMatrix) →
      LessEqual (upperValue transferMatrix) one

open TransferMatrixOrderData public

record WilsonTransferMatrixConclusion
    (Transfer Scalar : Set) : Set₁ where
  field
    orderData : TransferMatrixOrderData Transfer Scalar
    transferNonnegative :
      LessEqual orderData
        (zero orderData)
        (lowerValue orderData (transferMatrix orderData))
    transferContractive :
      LessEqual orderData
        (upperValue orderData (transferMatrix orderData))
        (one orderData)

open WilsonTransferMatrixConclusion public

record PhysicalWilsonOSIdentification
    (Observable Scalar : Set) : Set₁ where
  field
    publishedData : WilsonReflectionPositivityData Observable Scalar

    RepositoryWilsonAction : Set
    RepositoryPositiveTimeAlgebra : Set
    RepositoryGaugeInvariantObservables : Set

    repositoryWilsonAction : RepositoryWilsonAction
    repositoryPositiveTimeAlgebra : RepositoryPositiveTimeAlgebra
    repositoryGaugeInvariantObservables : RepositoryGaugeInvariantObservables

    actionMatchesPublishedWilsonConvention : Set
    positiveTimeAlgebraMatchesPublishedConvention : Set
    gaugeInvariantObservableMeaningMatches : Set

open PhysicalWilsonOSIdentification public

menottiPelissettoBibliographyLevel : ProofLevel
menottiPelissettoBibliographyLevel = computed

wilsonLinkPlaneReflectionPositivityLevel : ProofLevel
wilsonLinkPlaneReflectionPositivityLevel = standardImported

wilsonSitePlaneReflectionPositivityLevel : ProofLevel
wilsonSitePlaneReflectionPositivityLevel = standardImported

wilsonAllSeparationParityAssemblyLevel : ProofLevel
wilsonAllSeparationParityAssemblyLevel = machineChecked

wilsonTransferMatrixPositivityProvenanceLevel : ProofLevel
wilsonTransferMatrixPositivityProvenanceLevel = standardImported

physicalWilsonActionOSIdentificationInputsLevel : ProofLevel
physicalWilsonActionOSIdentificationInputsLevel = conditional

rgEffectiveActionReflectionPositivityPreservationInputsLevel : ProofLevel
rgEffectiveActionReflectionPositivityPreservationInputsLevel = conditional
