module DASHI.Biology.UniProtBH4PanelCertificateExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- EXACT UNIPROT 2026_03 BH4 / NOS / AAAH / AGMO / TSC2 / MTOR PANEL
--
-- Acquired 2026-10-17 with:
--   python3 scripts/acquire_uniprot_bio_certificate.py --kitzerow-bh4-panel
--
-- All sixteen requested records were acquired from one release with zero
-- failures.  Each row pins the raw REST response digest independently.
------------------------------------------------------------------------

record UniProtPanelCertificate : Set where
  constructor uniprot-panel-certificate
  field
    symbol : String
    accession : String
    sequenceLength : Nat
    md5 : String
    rawResponseSha256 : String
    release : String
    exactBinaryPinned : Bool

open UniProtPanelCertificate public

mkPinned : String → String → Nat → String → String → UniProtPanelCertificate
mkPinned symbol accession length md5 sha =
  uniprot-panel-certificate symbol accession length md5 sha "2026_03" true

gch1Certificate : UniProtPanelCertificate
gch1Certificate = mkPinned "GCH1" "P30793" 250 "72E739046638BE35430D36E6B787FEAB" "a56d2ea6bda05c47dacab457738c272f53ec58a53bcb12df88e2394797bd4fef"

gchfrCertificate : UniProtPanelCertificate
gchfrCertificate = mkPinned "GCHFR" "P30047" 84 "CA3CB80B149E05F4FCAD0EEAC1DAB250" "eb831eb3953ae991ed61616444f75eea67f636ad200cc31de1e0291eab931813"

ptsCertificate : UniProtPanelCertificate
ptsCertificate = mkPinned "PTS" "Q03393" 145 "AE36DC89898B673B0D5FBEADBD22EB79" "4fb18e9672a7f0330a71009e7225428906015b6cdf411a515cfb7504c52a1e03"

sprCertificate : UniProtPanelCertificate
sprCertificate = mkPinned "SPR" "P35270" 261 "72A33DA7FD5EE7948303B16773734FC0" "db2a1af14bef709926a7234847d1b733f0ffbb9d4e74bc8dacedf9a6ab2d5e75"

pcbd1Certificate : UniProtPanelCertificate
pcbd1Certificate = mkPinned "PCBD1" "P61457" 104 "C6EA7490F2747E501E1B05CFF8EB7B4E" "5d580818e01c137e501cc88bd7f3e0a993999076ef6adf397f3549f725b42a67"

qdprCertificate : UniProtPanelCertificate
qdprCertificate = mkPinned "QDPR" "P09417" 244 "01EAB47E5C55913647DB7DBAD571D960" "7ef73e73b15eb967db526cc5ba2970965992ff348e758b57057e1bc61def3936"

nos1Certificate : UniProtPanelCertificate
nos1Certificate = mkPinned "NOS1" "P29475" 1434 "5AF41AEA2622754A91E41D805DE51A55" "6580f22d9ec2ae7fb7466959a265bd1ad1906ca0254cd647ac75ab14267648ca"

nos2Certificate : UniProtPanelCertificate
nos2Certificate = mkPinned "NOS2" "P35228" 1153 "D1367AE563977E1B82EE63B017B07E1D" "4e4cd7f13d99d6710bb1c831970573fad6dae04a3d3bf199c14d03ec7103f025"

nos3Certificate : UniProtPanelCertificate
nos3Certificate = mkPinned "NOS3" "P29474" 1203 "738420F8D52B46F7C3A85F8DA8753B09" "9de31f7d180acd54d2007d34aa900053d0bcf30ff8eae24779f500a8b970c110"

pahCertificate : UniProtPanelCertificate
pahCertificate = mkPinned "PAH" "P00439" 452 "F233265AC67E981540E052978464F37E" "4a0e6ab4778f8d433f1e0c83646a6b37da1c7ee895a667c72b99440f5b5c0686"

thCertificate : UniProtPanelCertificate
thCertificate = mkPinned "TH" "P07101" 528 "D31975F3E1BFF5BB76AD85F03C3FAC84" "9911371e8e82f64e4154b4fbcb286ace5d3f48dd5834b2d0f89ea78bc23eb918"

tph1Certificate : UniProtPanelCertificate
tph1Certificate = mkPinned "TPH1" "P17752" 444 "8BC3C3E075D9941BBBD57789CF16AFEE" "fae1217cfc2ad1397192d5a286a10b5a24ff1ec6950a6aae583537f2eb4981ba"

tph2Certificate : UniProtPanelCertificate
tph2Certificate = mkPinned "TPH2" "Q8IWU9" 490 "9C5493F9ED5D7F64FD69F8D93C516505" "88eeacce7b1095c58d0650d719296f4e555e4e1d59fcc235a0828946bc6ab7ce"

agmoCertificate : UniProtPanelCertificate
agmoCertificate = mkPinned "AGMO" "Q6ZNB7" 445 "0CEB70A7F5E405E447B95BD988A65E9E" "f0b282ddeb04efa8840d400accedae5f377e5b34ad484ebd0260844ba93012ea"

tsc2Certificate : UniProtPanelCertificate
tsc2Certificate = mkPinned "TSC2" "P49815" 1807 "7B6AC7EBB4A2DFCB0DB2BBA352425BA5" "bb9b33894bdebbdc67b69e873ed8093a23d8f8e9bb7675f9321c69dc10e45310"

mtorCertificate : UniProtPanelCertificate
mtorCertificate = mkPinned "MTOR" "P42345" 2549 "D3BE1A657B7FDB5AB4C03E12D4452164" "ab0f7cd5427d5ab003220f6ddfc793b5c639389ef46c675ceb4a17ffcf183320"

allCertificates : List UniProtPanelCertificate
allCertificates =
  gch1Certificate ∷ gchfrCertificate ∷ ptsCertificate ∷ sprCertificate
  ∷ pcbd1Certificate ∷ qdprCertificate
  ∷ nos1Certificate ∷ nos2Certificate ∷ nos3Certificate
  ∷ pahCertificate ∷ thCertificate ∷ tph1Certificate ∷ tph2Certificate
  ∷ agmoCertificate ∷ tsc2Certificate ∷ mtorCertificate ∷ []

record UniProtBH4PanelBoundary : Set where
  constructor uniprot-bh4-panel-boundary
  field
    requestedMembers : Nat
    acquiredMembers : Nat
    failedMembers : Nat
    oneReleaseSet : Bool
    everyMemberBytePinned : Bool
    completePanelCreatesWholeModelConfirmation : Bool
    completePanelCreatesWholeModelConfirmationIsFalse :
      completePanelCreatesWholeModelConfirmation ≡ false
    completePanelCreatesAllocatorFlux : Bool
    completePanelCreatesAllocatorFluxIsFalse :
      completePanelCreatesAllocatorFlux ≡ false

open UniProtBH4PanelBoundary public

canonicalUniProtBH4PanelBoundary : UniProtBH4PanelBoundary
canonicalUniProtBH4PanelBoundary =
  uniprot-bh4-panel-boundary 16 16 0 true true false refl false refl

canonicalUniProtBH4PanelReceipt : Receipt.GenericReceipt
canonicalUniProtBH4PanelReceipt =
  Receipt.mkNonPromotingReceipt
    "exact UniProt BH4 system panel"
    "DASHI.Biology.UniProtBH4PanelCertificateExact"
    "16/16 UniProtKB 2026_03 records with per-response SHA-256 and sequence MD5"
    "closes the external protein-record acquisition residual for GCH1/GCHFR/PTS/SPR/PCBD1/QDPR/NOS1-3/PAH/TH/TPH1-2/AGMO/TSC2/MTOR"
    "complete exact protein acquisition does not create compartmental flux, consumer competition, NOS uncoupling, disease causality or whole-model confirmation"
    "python3 scripts/acquire_uniprot_bio_certificate.py --kitzerow-bh4-panel"
