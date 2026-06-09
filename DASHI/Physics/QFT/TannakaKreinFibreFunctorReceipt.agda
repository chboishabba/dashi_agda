module DASHI.Physics.QFT.TannakaKreinFibreFunctorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.FinitePrimeLaneDHRSMCompatibilityLedger as FiniteLedger

------------------------------------------------------------------------
-- Tannaka-Krein finite fibre-functor receipt.
--
-- This is a finite, prime-lane-only receipt.  It records the current p2, p3,
-- and p5 carrier rows as a fibre functor into finite Hilbert-dimension
-- targets n2=1, n3=2, n5=3.  The monoidal structure recorded here is the
-- finite carrier-pair wiring already present in the prime-lane ledger.  It is
-- not a construction of the full DHR compact dual group.

data TannakaKreinAuthorityCitation : Set where
  tannakaKreinCompactGroupDuality :
    TannakaKreinAuthorityCitation

  deligneTannakianCategories :
    TannakaKreinAuthorityCitation

  doplicherRobertsDHRReconstruction :
    TannakaKreinAuthorityCitation

canonicalTannakaKreinAuthorityCitations :
  List TannakaKreinAuthorityCitation
canonicalTannakaKreinAuthorityCitations =
  tannakaKreinCompactGroupDuality
  ∷ deligneTannakianCategories
  ∷ doplicherRobertsDHRReconstruction
  ∷ []

data TannakaKreinFibreFunctorAuthorityBoundary : Set where
  externalTannakaKreinAuthorityRequiredForAutTensorF :
    TannakaKreinFibreFunctorAuthorityBoundary

data TannakaKreinDualGroupTarget : Set where
  autTensorFIsGDHRTargetOnly :
    TannakaKreinDualGroupTarget

finitePrimeLaneHilbertDimension :
  FiniteLedger.FinitePrimeLaneLocalisedEndomorphismKind →
  Nat
finitePrimeLaneHilbertDimension
  FiniteLedger.p2CarrierLocalisedEndomorphism =
  1
finitePrimeLaneHilbertDimension
  FiniteLedger.p3CarrierLocalisedEndomorphism =
  2
finitePrimeLaneHilbertDimension
  FiniteLedger.p5CarrierLocalisedEndomorphism =
  3

record FinitePrimeLaneFibreFunctorRow
  (lane : FiniteLedger.FinitePrimeLaneLocalisedEndomorphismKind) :
  Set₁ where
  field
    sourceRow :
      FiniteLedger.FinitePrimeLaneSMRow

    sourceRowIsCanonical :
      sourceRow
      ≡
      FiniteLedger.finitePrimeLaneLocalisedEndomorphismRow lane

    fibreCarrier :
      Set

    fibreCarrierIsLaneCarrier :
      fibreCarrier
      ≡
      FiniteLedger.finitePrimeLaneLocalisedEndomorphismCarrier lane

    selectedFibreVector :
      FiniteLedger.finitePrimeLaneLocalisedEndomorphismCarrier lane

    selectedFibreVectorIsCanonical :
      selectedFibreVector
      ≡
      FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier lane

    hilbertDimension :
      Nat

    hilbertDimensionIsPrimeLaneDimension :
      hilbertDimension
      ≡
      finitePrimeLaneHilbertDimension lane

    hilbertDimensionMatchesLedgerRow :
      hilbertDimension
      ≡
      FiniteLedger.FinitePrimeLaneSMRow.gaugeDimension sourceRow

    rowBoundary :
      List String

open FinitePrimeLaneFibreFunctorRow public

p2FinitePrimeLaneFibreFunctorRow :
  FinitePrimeLaneFibreFunctorRow
    FiniteLedger.p2CarrierLocalisedEndomorphism
p2FinitePrimeLaneFibreFunctorRow =
  record
    { sourceRow =
        FiniteLedger.p2U1YFinitePrimeLaneSMRow
    ; sourceRowIsCanonical =
        refl
    ; fibreCarrier =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismCarrier
          FiniteLedger.p2CarrierLocalisedEndomorphism
    ; fibreCarrierIsLaneCarrier =
        refl
    ; selectedFibreVector =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p2CarrierLocalisedEndomorphism
    ; selectedFibreVectorIsCanonical =
        refl
    ; hilbertDimension =
        1
    ; hilbertDimensionIsPrimeLaneDimension =
        refl
    ; hilbertDimensionMatchesLedgerRow =
        refl
    ; rowBoundary =
        "F(p2) is the finite one-dimensional Hilbert fibre carried by the p2/U1Y ledger row"
        ∷ "The selected p2 fibre vector is the existing p2 scalar carrier point"
        ∷ []
    }

p3FinitePrimeLaneFibreFunctorRow :
  FinitePrimeLaneFibreFunctorRow
    FiniteLedger.p3CarrierLocalisedEndomorphism
p3FinitePrimeLaneFibreFunctorRow =
  record
    { sourceRow =
        FiniteLedger.p3SU2LFinitePrimeLaneSMRow
    ; sourceRowIsCanonical =
        refl
    ; fibreCarrier =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismCarrier
          FiniteLedger.p3CarrierLocalisedEndomorphism
    ; fibreCarrierIsLaneCarrier =
        refl
    ; selectedFibreVector =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p3CarrierLocalisedEndomorphism
    ; selectedFibreVectorIsCanonical =
        refl
    ; hilbertDimension =
        2
    ; hilbertDimensionIsPrimeLaneDimension =
        refl
    ; hilbertDimensionMatchesLedgerRow =
        refl
    ; rowBoundary =
        "F(p3) is the finite two-dimensional Hilbert fibre carried by the p3/SU2L ledger row"
        ∷ "The selected p3 fibre vector is the existing M2-basis carrier point"
        ∷ []
    }

p5FinitePrimeLaneFibreFunctorRow :
  FinitePrimeLaneFibreFunctorRow
    FiniteLedger.p5CarrierLocalisedEndomorphism
p5FinitePrimeLaneFibreFunctorRow =
  record
    { sourceRow =
        FiniteLedger.p5SU3cFinitePrimeLaneSMRow
    ; sourceRowIsCanonical =
        refl
    ; fibreCarrier =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismCarrier
          FiniteLedger.p5CarrierLocalisedEndomorphism
    ; fibreCarrierIsLaneCarrier =
        refl
    ; selectedFibreVector =
        FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p5CarrierLocalisedEndomorphism
    ; selectedFibreVectorIsCanonical =
        refl
    ; hilbertDimension =
        3
    ; hilbertDimensionIsPrimeLaneDimension =
        refl
    ; hilbertDimensionMatchesLedgerRow =
        refl
    ; rowBoundary =
        "F(p5) is the finite three-dimensional Hilbert fibre carried by the p5/SU3c ledger row"
        ∷ "The selected p5 fibre vector is the existing M3 carrier point"
        ∷ []
    }

record FinitePrimeLaneFibreFunctorMonoidalStructure : Set₁ where
  field
    p2p3TensorFibre :
      FiniteLedger.FinitePrimeLaneCarrierPair
        FiniteLedger.p2CarrierLocalisedEndomorphism
        FiniteLedger.p3CarrierLocalisedEndomorphism

    p2p3TensorFibreIsSelectedPair :
      p2p3TensorFibre
      ≡
      FiniteLedger.finitePrimeLaneCarrierPair
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p2CarrierLocalisedEndomorphism)
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p3CarrierLocalisedEndomorphism)

    p3p5TensorFibre :
      FiniteLedger.FinitePrimeLaneCarrierPair
        FiniteLedger.p3CarrierLocalisedEndomorphism
        FiniteLedger.p5CarrierLocalisedEndomorphism

    p3p5TensorFibreIsSelectedPair :
      p3p5TensorFibre
      ≡
      FiniteLedger.finitePrimeLaneCarrierPair
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p3CarrierLocalisedEndomorphism)
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p5CarrierLocalisedEndomorphism)

    p5p2TensorFibre :
      FiniteLedger.FinitePrimeLaneCarrierPair
        FiniteLedger.p5CarrierLocalisedEndomorphism
        FiniteLedger.p2CarrierLocalisedEndomorphism

    p5p2TensorFibreIsSelectedPair :
      p5p2TensorFibre
      ≡
      FiniteLedger.finitePrimeLaneCarrierPair
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p5CarrierLocalisedEndomorphism)
        (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
          FiniteLedger.p2CarrierLocalisedEndomorphism)

    p2p3PairActionIdentity :
      FiniteLedger.finitePrimeLaneCarrierPairAction
        FiniteLedger.p2CarrierLocalisedEndomorphism
        FiniteLedger.p3CarrierLocalisedEndomorphism
        p2p3TensorFibre
      ≡
      p2p3TensorFibre

    p3p5PairActionIdentity :
      FiniteLedger.finitePrimeLaneCarrierPairAction
        FiniteLedger.p3CarrierLocalisedEndomorphism
        FiniteLedger.p5CarrierLocalisedEndomorphism
        p3p5TensorFibre
      ≡
      p3p5TensorFibre

    p5p2PairActionIdentity :
      FiniteLedger.finitePrimeLaneCarrierPairAction
        FiniteLedger.p5CarrierLocalisedEndomorphism
        FiniteLedger.p2CarrierLocalisedEndomorphism
        p5p2TensorFibre
      ≡
      p5p2TensorFibre

    finiteMonoidalStructureRecorded :
      Bool

    finiteMonoidalStructureRecordedIsTrue :
      finiteMonoidalStructureRecorded ≡ true

    fullDHRMonoidalFunctorConstructed :
      Bool

    fullDHRMonoidalFunctorConstructedIsFalse :
      fullDHRMonoidalFunctorConstructed ≡ false

    monoidalBoundary :
      List String

open FinitePrimeLaneFibreFunctorMonoidalStructure public

canonicalFinitePrimeLaneFibreFunctorMonoidalStructure :
  FinitePrimeLaneFibreFunctorMonoidalStructure
canonicalFinitePrimeLaneFibreFunctorMonoidalStructure =
  record
    { p2p3TensorFibre =
        FiniteLedger.finitePrimeLaneCarrierPair
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p2CarrierLocalisedEndomorphism)
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p3CarrierLocalisedEndomorphism)
    ; p2p3TensorFibreIsSelectedPair =
        refl
    ; p3p5TensorFibre =
        FiniteLedger.finitePrimeLaneCarrierPair
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p3CarrierLocalisedEndomorphism)
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p5CarrierLocalisedEndomorphism)
    ; p3p5TensorFibreIsSelectedPair =
        refl
    ; p5p2TensorFibre =
        FiniteLedger.finitePrimeLaneCarrierPair
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p5CarrierLocalisedEndomorphism)
          (FiniteLedger.finitePrimeLaneLocalisedEndomorphismSelectedCarrier
            FiniteLedger.p2CarrierLocalisedEndomorphism)
    ; p5p2TensorFibreIsSelectedPair =
        refl
    ; p2p3PairActionIdentity =
        refl
    ; p3p5PairActionIdentity =
        refl
    ; p5p2PairActionIdentity =
        refl
    ; finiteMonoidalStructureRecorded =
        true
    ; finiteMonoidalStructureRecordedIsTrue =
        refl
    ; fullDHRMonoidalFunctorConstructed =
        false
    ; fullDHRMonoidalFunctorConstructedIsFalse =
        refl
    ; monoidalBoundary =
        "The finite monoidal structure is the selected carrier-pair wiring for p2/p3, p3/p5, and p5/p2"
        ∷ "Pair actions reduce definitionally to identity because the finite prime-lane endomorphism actions are identity actions"
        ∷ "This is not a full monoidal functor on arbitrary DHR sectors"
        ∷ []
    }

record TannakaKreinFibreFunctorReceipt : Setω where
  field
    finiteLedgerRows :
      List FiniteLedger.FinitePrimeLaneSMRow

    finiteLedgerRowsSelectedCanonical :
      Bool

    finiteLedgerRowsSelectedCanonicalIsTrue :
      finiteLedgerRowsSelectedCanonical ≡ true

    p2FibreRow :
      FinitePrimeLaneFibreFunctorRow
        FiniteLedger.p2CarrierLocalisedEndomorphism

    p2FibreRowIsCanonical :
      p2FibreRow ≡ p2FinitePrimeLaneFibreFunctorRow

    p3FibreRow :
      FinitePrimeLaneFibreFunctorRow
        FiniteLedger.p3CarrierLocalisedEndomorphism

    p3FibreRowIsCanonical :
      p3FibreRow ≡ p3FinitePrimeLaneFibreFunctorRow

    p5FibreRow :
      FinitePrimeLaneFibreFunctorRow
        FiniteLedger.p5CarrierLocalisedEndomorphism

    p5FibreRowIsCanonical :
      p5FibreRow ≡ p5FinitePrimeLaneFibreFunctorRow

    p2HilbertDimension :
      Nat

    p2HilbertDimensionIsOne :
      p2HilbertDimension ≡ 1

    p3HilbertDimension :
      Nat

    p3HilbertDimensionIsTwo :
      p3HilbertDimension ≡ 2

    p5HilbertDimension :
      Nat

    p5HilbertDimensionIsThree :
      p5HilbertDimension ≡ 3

    finiteMonoidalStructure :
      FinitePrimeLaneFibreFunctorMonoidalStructure

    finiteMonoidalStructureIsCanonical :
      finiteMonoidalStructure
      ≡
      canonicalFinitePrimeLaneFibreFunctorMonoidalStructure

    authorityCitations :
      List TannakaKreinAuthorityCitation

    authorityCitationsAreCanonical :
      authorityCitations ≡ canonicalTannakaKreinAuthorityCitations

    deligneAuthorityIdentifier :
      String

    deligneAuthorityIdentifierIsMath0206028 :
      deligneAuthorityIdentifier ≡ "arXiv:math/0206028"

    tannakaReconstructionStatement :
      String

    tannakaReconstructionStatementIsScoped :
      tannakaReconstructionStatement
      ≡
      "Aut^tensor(F)-is-the-DHR-compact-dual-group-by-external-Tannaka-Krein-Deligne-authority"

    autTensorFEquivalentGDHRTarget :
      TannakaKreinDualGroupTarget

    autTensorFEquivalentGDHRTargetIsAuthorityOnly :
      autTensorFEquivalentGDHRTarget ≡ autTensorFIsGDHRTargetOnly

    authorityBoundary :
      TannakaKreinFibreFunctorAuthorityBoundary

    authorityBoundaryIsExternalTannakaKrein :
      authorityBoundary
      ≡
      externalTannakaKreinAuthorityRequiredForAutTensorF

    compactGaugeGroupTarget :
      DHR.CompactGaugeGroup

    compactGaugeGroupTargetIsDHRAbstract :
      compactGaugeGroupTarget ≡ DHR.abstractCompactGaugeGroup

    finiteFibreFunctorRecorded :
      Bool

    finiteFibreFunctorRecordedIsTrue :
      finiteFibreFunctorRecorded ≡ true

    tannakaDualGroupConstructed :
      Bool

    tannakaDualGroupConstructedIsFalse :
      tannakaDualGroupConstructed ≡ false

    autTensorFComputedLocally :
      Bool

    autTensorFComputedLocallyIsFalse :
      autTensorFComputedLocally ≡ false

    gDHREqualsSMGaugePromoted :
      Bool

    gDHREqualsSMGaugePromotedIsFalse :
      gDHREqualsSMGaugePromoted ≡ false

    receiptBoundary :
      List String

open TannakaKreinFibreFunctorReceipt public

canonicalTannakaKreinFibreFunctorReceipt :
  TannakaKreinFibreFunctorReceipt
canonicalTannakaKreinFibreFunctorReceipt =
  record
    { finiteLedgerRows =
        FiniteLedger.canonicalFinitePrimeLaneSMRows
    ; finiteLedgerRowsSelectedCanonical =
        true
    ; finiteLedgerRowsSelectedCanonicalIsTrue =
        refl
    ; p2FibreRow =
        p2FinitePrimeLaneFibreFunctorRow
    ; p2FibreRowIsCanonical =
        refl
    ; p3FibreRow =
        p3FinitePrimeLaneFibreFunctorRow
    ; p3FibreRowIsCanonical =
        refl
    ; p5FibreRow =
        p5FinitePrimeLaneFibreFunctorRow
    ; p5FibreRowIsCanonical =
        refl
    ; p2HilbertDimension =
        1
    ; p2HilbertDimensionIsOne =
        refl
    ; p3HilbertDimension =
        2
    ; p3HilbertDimensionIsTwo =
        refl
    ; p5HilbertDimension =
        3
    ; p5HilbertDimensionIsThree =
        refl
    ; finiteMonoidalStructure =
        canonicalFinitePrimeLaneFibreFunctorMonoidalStructure
    ; finiteMonoidalStructureIsCanonical =
        refl
    ; authorityCitations =
        canonicalTannakaKreinAuthorityCitations
    ; authorityCitationsAreCanonical =
        refl
    ; deligneAuthorityIdentifier =
        "arXiv:math/0206028"
    ; deligneAuthorityIdentifierIsMath0206028 =
        refl
    ; tannakaReconstructionStatement =
        "Aut^tensor(F)-is-the-DHR-compact-dual-group-by-external-Tannaka-Krein-Deligne-authority"
    ; tannakaReconstructionStatementIsScoped =
        refl
    ; autTensorFEquivalentGDHRTarget =
        autTensorFIsGDHRTargetOnly
    ; autTensorFEquivalentGDHRTargetIsAuthorityOnly =
        refl
    ; authorityBoundary =
        externalTannakaKreinAuthorityRequiredForAutTensorF
    ; authorityBoundaryIsExternalTannakaKrein =
        refl
    ; compactGaugeGroupTarget =
        DHR.abstractCompactGaugeGroup
    ; compactGaugeGroupTargetIsDHRAbstract =
        refl
    ; finiteFibreFunctorRecorded =
        true
    ; finiteFibreFunctorRecordedIsTrue =
        refl
    ; tannakaDualGroupConstructed =
        false
    ; tannakaDualGroupConstructedIsFalse =
        refl
    ; autTensorFComputedLocally =
        false
    ; autTensorFComputedLocallyIsFalse =
        refl
    ; gDHREqualsSMGaugePromoted =
        false
    ; gDHREqualsSMGaugePromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite fibre functor records F(p2)=Hilb_1, F(p3)=Hilb_2, and F(p5)=Hilb_3 using the existing finite prime-lane ledger carriers"
        ∷ "The monoidal structure recorded here is finite selected carrier-pair wiring only"
        ∷ "External Deligne/Tannaka-Krein/Doplicher-Roberts authority is recorded for the target Aut^tensor(F) ~= G_DHR"
        ∷ "No local computation of Aut^tensor(F), compact DHR dual group, full DHR fibre functor, or G_DHR ~= Standard Model gauge is promoted"
        ∷ []
    }

tannakaKreinFiniteFibreFunctorRecorded :
  TannakaKreinFibreFunctorReceipt.finiteFibreFunctorRecorded
    canonicalTannakaKreinFibreFunctorReceipt
  ≡
  true
tannakaKreinFiniteFibreFunctorRecorded =
  refl

tannakaKreinDualGroupNotConstructed :
  TannakaKreinFibreFunctorReceipt.tannakaDualGroupConstructed
    canonicalTannakaKreinFibreFunctorReceipt
  ≡
  false
tannakaKreinDualGroupNotConstructed =
  refl
