module LargerObjectClassificationLattice where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Larger formalism object-family status classifier.
--
-- This is an inventory lattice for object families that appear across the
-- DASHI/SensibLaw/PNF/physics receipt surface. It classifies the current
-- formal status of the object family. It does not promote named receipt
-- surfaces into theorems and does not collapse bridges into equivalences.

data LargerObjectFamily : Set where
  loomTrajectoryObject : LargerObjectFamily
  affidavitRelationObject : LargerObjectFamily
  claimAtomObject : LargerObjectFamily
  contestedClaimObject : LargerObjectFamily
  typedObjectAssertionObject : LargerObjectFamily
  morphismTypingClaimObject : LargerObjectFamily
  wikidataStatementRowObject : LargerObjectFamily
  wikidataQualifierObject : LargerObjectFamily
  wikidataReferenceObject : LargerObjectFamily
  wikidataRevisionWindowObject : LargerObjectFamily
  wikidataLiveEditAuthorityObject : LargerObjectFamily
  wikidataTruthAuthorityObject : LargerObjectFamily
  pnfResidualObject : LargerObjectFamily
  pnfRuntimeReceiptObject : LargerObjectFamily
  heckeDefectObject : LargerObjectFamily
  heckeCandidateFibreObject : LargerObjectFamily
  heckeEigenObject : LargerObjectFamily
  eigenvalueObject : LargerObjectFamily
  eigenbasisObject : LargerObjectFamily
  eigenspaceObject : LargerObjectFamily
  kolmogorovScaleObject : LargerObjectFamily
  nsSerrinClassObject : LargerObjectFamily
  bottKTheoryObject : LargerObjectFamily
  cliffordBridgeObject : LargerObjectFamily
  monsterMoonshineObject : LargerObjectFamily
  monsterIrrepObject : LargerObjectFamily
  dnaEigenclassObject : LargerObjectFamily
  brainEigenbasisObject : LargerObjectFamily
  brainSemanticTransportObject : LargerObjectFamily
  brainDnaConnectorObject : LargerObjectFamily

canonicalLargerObjectFamilies : List LargerObjectFamily
canonicalLargerObjectFamilies =
  loomTrajectoryObject
  ∷ affidavitRelationObject
  ∷ claimAtomObject
  ∷ contestedClaimObject
  ∷ typedObjectAssertionObject
  ∷ morphismTypingClaimObject
  ∷ wikidataStatementRowObject
  ∷ wikidataQualifierObject
  ∷ wikidataReferenceObject
  ∷ wikidataRevisionWindowObject
  ∷ wikidataLiveEditAuthorityObject
  ∷ wikidataTruthAuthorityObject
  ∷ pnfResidualObject
  ∷ pnfRuntimeReceiptObject
  ∷ heckeDefectObject
  ∷ heckeCandidateFibreObject
  ∷ heckeEigenObject
  ∷ eigenvalueObject
  ∷ eigenbasisObject
  ∷ eigenspaceObject
  ∷ kolmogorovScaleObject
  ∷ nsSerrinClassObject
  ∷ bottKTheoryObject
  ∷ cliffordBridgeObject
  ∷ monsterMoonshineObject
  ∷ monsterIrrepObject
  ∷ dnaEigenclassObject
  ∷ brainEigenbasisObject
  ∷ brainSemanticTransportObject
  ∷ brainDnaConnectorObject
  ∷ []

data LargerObjectStatus : Set where
  classified : LargerObjectStatus
  bridged : LargerObjectStatus
  receiptSurface : LargerObjectStatus
  scaffoldOnly : LargerObjectStatus
  runtimePending : LargerObjectStatus
  promotionBlocked : LargerObjectStatus
  outsideCurrentClassifier : LargerObjectStatus

canonicalLargerObjectStatuses : List LargerObjectStatus
canonicalLargerObjectStatuses =
  classified
  ∷ bridged
  ∷ receiptSurface
  ∷ scaffoldOnly
  ∷ runtimePending
  ∷ promotionBlocked
  ∷ outsideCurrentClassifier
  ∷ []

data LargerObjectRelationRoot : Set where
  objectClassified : LargerObjectRelationRoot
  objectBridged : LargerObjectRelationRoot
  objectReceiptOnly : LargerObjectRelationRoot
  objectScaffold : LargerObjectRelationRoot
  objectAwaitingRuntime : LargerObjectRelationRoot
  objectPromotionBlocked : LargerObjectRelationRoot
  objectOutOfScope : LargerObjectRelationRoot

relationRootForStatus : LargerObjectStatus → LargerObjectRelationRoot
relationRootForStatus classified = objectClassified
relationRootForStatus bridged = objectBridged
relationRootForStatus receiptSurface = objectReceiptOnly
relationRootForStatus scaffoldOnly = objectScaffold
relationRootForStatus runtimePending = objectAwaitingRuntime
relationRootForStatus promotionBlocked = objectPromotionBlocked
relationRootForStatus outsideCurrentClassifier = objectOutOfScope

record LargerObjectClassification : Set where
  constructor largerObjectClassification
  field
    family :
      LargerObjectFamily

    status :
      LargerObjectStatus

    relationRoot :
      LargerObjectRelationRoot

    relationRootIsDerived :
      relationRoot ≡ relationRootForStatus status

    promotionFalse :
      Bool

    promotionFalseIsTrue :
      promotionFalse ≡ true

    statusNote :
      String

open LargerObjectClassification public
open LargerObjectFamily public
open LargerObjectStatus public
open LargerObjectRelationRoot public

classify :
  LargerObjectFamily →
  LargerObjectStatus →
  String →
  LargerObjectClassification
classify family status note =
  largerObjectClassification
    family
    status
    (relationRootForStatus status)
    refl
    true
    refl
    note

canonicalLargerObjectClassifications :
  List LargerObjectClassification
canonicalLargerObjectClassifications =
  classify
    loomTrajectoryObject
    classified
    "Loom trajectories are classified by the finite affidavit-style relation algebra; edge family remains visual provenance."
  ∷ classify
    affidavitRelationObject
    classified
    "Affidavit relation labels, roots, buckets, evidence states, and promotion states are finite typed objects."
  ∷ classify
    claimAtomObject
    classified
    "Normalized claim atoms are classified as proposition carriers with polarity, source kind, provenance, and non-promotion state."
  ∷ classify
    contestedClaimObject
    classified
    "Contested claim pairs are classified by finite reconciliation relations such as explicit dispute, not by truth decision."
  ∷ classify
    typedObjectAssertionObject
    classified
    "Typed-object assertions are classified as claim carriers requiring explicit context and witnesses for stronger use."
  ∷ classify
    morphismTypingClaimObject
    runtimePending
    "Claims such as 6 is a 1-morphism remain witness-pending until category/context and typing rules are supplied."
  ∷ classify
    wikidataStatementRowObject
    classified
    "Wikidata statement rows are classified as QID/PID/value evidence carriers with bounded review status."
  ∷ classify
    wikidataQualifierObject
    classified
    "Wikidata qualifiers are first-class scope and drift carriers, not hidden metadata."
  ∷ classify
    wikidataReferenceObject
    classified
    "Wikidata references are provenance handles for row review, not proof witnesses for real-world truth."
  ∷ classify
    wikidataRevisionWindowObject
    classified
    "Wikidata revision/window carriers bound row comparison without live global dependency."
  ∷ classify
    wikidataLiveEditAuthorityObject
    promotionBlocked
    "Live Wikidata edit authority is explicitly blocked in this formal classifier."
  ∷ classify
    wikidataTruthAuthorityObject
    promotionBlocked
    "Wikidata truth authority is explicitly blocked; rows are review/provenance carriers only."
  ∷ classify
    pnfResidualObject
    classified
    "PNF residual levels remain exact, partial, no typed meet, and contradiction."
  ∷ classify
    pnfRuntimeReceiptObject
    runtimePending
    "Parser/runtime PNF receipts are consumed when emitted; they are not statically closed here."
  ∷ classify
    heckeDefectObject
    classified
    "Hecke defect classes are mapped into PNF residual levels by the Hecke residual bridge."
  ∷ classify
    heckeCandidateFibreObject
    bridged
    "Same-Hecke quotient fibres are candidate pools, not eigenclassification closure."
  ∷ classify
    heckeEigenObject
    receiptSurface
    "Hecke eigen objects exist as receipt surfaces but are not globally normalized into this classifier."
  ∷ classify
    eigenvalueObject
    receiptSurface
    "Eigenvalue receipts are evidence surfaces; no global eigenvalue taxonomy is closed here."
  ∷ classify
    eigenbasisObject
    receiptSurface
    "Eigenbasis receipts are tracked as surfaces and bridge obligations, not promoted equivalences."
  ∷ classify
    eigenspaceObject
    receiptSurface
    "Eigenspace classification receipts remain local surfaces unless a separate bridge closes them."
  ∷ classify
    kolmogorovScaleObject
    receiptSurface
    "Kolmogorov-scale and admissibility receipts are present but outside this classifier's closed algebra."
  ∷ classify
    nsSerrinClassObject
    promotionBlocked
    "NS/Serrin classes are boundary receipts here; no Navier-Stokes theorem claim is promoted."
  ∷ classify
    bottKTheoryObject
    scaffoldOnly
    "Bott/K-theory material is a scaffold and obligation surface only."
  ∷ classify
    cliffordBridgeObject
    bridged
    "Clifford bridge receipts are typed obligations; they do not imply Cl(0,6) equivalence promotion."
  ∷ classify
    monsterMoonshineObject
    receiptSurface
    "Monster moonshine objects are receipt surfaces, not a closed global moonshine classifier."
  ∷ classify
    monsterIrrepObject
    receiptSurface
    "Monster irrep carrier receipts are tracked locally and remain non-promoting."
  ∷ classify
    dnaEigenclassObject
    classified
    "DNA eigenclass surfaces have local classifiers, not closed biological or spectral theorem promotions."
  ∷ classify
    brainEigenbasisObject
    classified
    "Brain eigenbasis phases have local classifiers and do not promote cognitive-state theorems."
  ∷ classify
    brainSemanticTransportObject
    bridged
    "Brain semantic transport is a bridge surface whose claims require separate witnesses."
  ∷ classify
    brainDnaConnectorObject
    bridged
    "Brain-DNA connector objects are compatibility bridges, not merged ontological classes."
  ∷ []

record LargerObjectClassificationLattice : Set where
  field
    families :
      List LargerObjectFamily

    familiesAreCanonical :
      families ≡ canonicalLargerObjectFamilies

    statuses :
      List LargerObjectStatus

    statusesAreCanonical :
      statuses ≡ canonicalLargerObjectStatuses

    classifications :
      List LargerObjectClassification

    classificationsAreCanonical :
      classifications ≡ canonicalLargerObjectClassifications

    largerFormalismBoundary :
      List String

    promotionSeparated :
      Bool

    promotionSeparatedIsTrue :
      promotionSeparated ≡ true

    scopeSummary :
      String

open LargerObjectClassificationLattice public

canonicalLargerObjectClassificationLattice :
  LargerObjectClassificationLattice
canonicalLargerObjectClassificationLattice =
  record
    { families =
        canonicalLargerObjectFamilies
    ; familiesAreCanonical =
        refl
    ; statuses =
        canonicalLargerObjectStatuses
    ; statusesAreCanonical =
        refl
    ; classifications =
        canonicalLargerObjectClassifications
    ; classificationsAreCanonical =
        refl
    ; largerFormalismBoundary =
        "Classified means the finite object/status relation is typed here; it does not mean theorem promotion."
        ∷ "Bridged means a typed connection or candidate fibre exists but a separate witness must close stronger claims."
        ∷ "Receipt surface means the object family is named and evidenced locally but is not globally normalized."
        ∷ "Promotion-blocked means the object family is deliberately prevented from becoming a theorem claim in this lane."
        ∷ []
    ; promotionSeparated =
        true
    ; promotionSeparatedIsTrue =
        refl
    ; scopeSummary =
        "The larger formalism currently classifies status of object families, not all internal mathematical inhabitants."
    }
