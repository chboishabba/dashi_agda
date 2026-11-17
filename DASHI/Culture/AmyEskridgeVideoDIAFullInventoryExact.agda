module DASHI.Culture.AmyEskridgeVideoDIAFullInventoryExact where

-- Exact transcription of the 37 entries on the two original DIA inventory
-- pages of FOIA-00159-2018 (DIA response dated 2022-03-25).
-- Holder/requester: DIA / John Greenewald (The Black Vault).
-- Source: https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf
-- Inventory PDF pages 4 and 5; titles preserve official spelling/OCR where
-- misleadingly worded. The 37-row list totals 1,473 declared pages.
-- Four full PDFs (#13, #15, #18, #19) are recorded elsewhere as inspected.
-- The other 33 entries are title/page-count metadata ONLY.
-- No claim of independent test, success, programme ownership or "38 files"
-- may arise from this index. Source attribution policy:
-- Docs/SourceAttributionPolicy.md.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Core.Prelude using (⊥)
import DASHI.Core.AttributedSourceCore as A
import DASHI.Culture.AmyEskridgeVideoPrimaryInspectionExact as Inspected

dia2022InventoryAuthority : A.AttributedSource
dia2022InventoryAuthority = A.mkNoDOISource
  "U.S. Defense Intelligence Agency; FOIA requester John Greenewald"
  "FOIA-00159-2018, response U-22-7061/IMO-2 and 37-item DIRD inventory"
  "DIA FOIA response letter and inventory, original PDF pp. 1, 4-5"
  "2022"
  "https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf"
  A.governmentSource
  "Source metadata: exactly 37 indexed titles and 1473 listed pages; the individual report text was separately inspected only for four studies"
  A.publicAttribution

data ReadDepth : Set where
  inventoryTitleOnly : ReadDepth
  releasedReportInspected : ReadDepth

record DIRDInventoryEntry : Set where
  constructor dird-entry
  field
    inventoryNumber : Nat
    inventoryTitle : String
    listedPages : Nat
    reading : ReadDepth
    inventorySource : A.AttributedSource
open DIRDInventoryEntry public

dird01 : DIRDInventoryEntry
dird01 = dird-entry 1 "Metallic Glasses - Status and Prospects for Aerospace Applications" 30 inventoryTitleOnly dia2022InventoryAuthority

dird02 : DIRDInventoryEntry
dird02 = dird-entry 2 "Aerospace Applications of Programmable Matter" 20 inventoryTitleOnly dia2022InventoryAuthority

dird03 : DIRDInventoryEntry
dird03 = dird-entry 3 "Pulsed High-Power Microwave Source Technology" 37 inventoryTitleOnly dia2022InventoryAuthority

dird04 : DIRDInventoryEntry
dird04 = dird-entry 4 "Biomaterials" 32 inventoryTitleOnly dia2022InventoryAuthority

dird05 : DIRDInventoryEntry
dird05 = dird-entry 5 "Materials for Advanced Aerospace Platforms" 27 inventoryTitleOnly dia2022InventoryAuthority

dird06 : DIRDInventoryEntry
dird06 = dird-entry 6 "Space Access - Where We've Been and Where We Could Go" 56 inventoryTitleOnly dia2022InventoryAuthority

dird07 : DIRDInventoryEntry
dird07 = dird-entry 7 "Invisibilty Cloaking - Theory and Experiments" 29 inventoryTitleOnly dia2022InventoryAuthority

dird08 : DIRDInventoryEntry
dird08 = dird-entry 8 "Positron Aerospace Propulsion" 35 inventoryTitleOnly dia2022InventoryAuthority

dird09 : DIRDInventoryEntry
dird09 = dird-entry 9 "Inertial Electrostatic Confinement Fusion" 72 inventoryTitleOnly dia2022InventoryAuthority

dird10 : DIRDInventoryEntry
dird10 = dird-entry 10 "Metallic Spintronics" 27 inventoryTitleOnly dia2022InventoryAuthority

dird11 : DIRDInventoryEntry
dird11 = dird-entry 11 "Advanced Nuclear Propulsion For Manned Deep Space Missions" 37 inventoryTitleOnly dia2022InventoryAuthority

dird12 : DIRDInventoryEntry
dird12 = dird-entry 12 "Technological Approaches to Controlling External Devices" 36 inventoryTitleOnly dia2022InventoryAuthority

dird13 : DIRDInventoryEntry
dird13 = dird-entry 13 "Warp Drive, Dark Energy, and the Manipulation of Extra Dimensions" 33 releasedReportInspected dia2022InventoryAuthority

dird14 : DIRDInventoryEntry
dird14 = dird-entry 14 "The Role of Superconductors in Gravity Research" 16 inventoryTitleOnly dia2022InventoryAuthority

dird15 : DIRDInventoryEntry
dird15 = dird-entry 15 "Advanced Space Propulson Based on Vacuum (Spacetime Metric) Engineer" 17 releasedReportInspected dia2022InventoryAuthority

dird16 : DIRDInventoryEntry
dird16 = dird-entry 16 "The Space Communication Implications of Quantum Entanglement and Nonlocality" 32 inventoryTitleOnly dia2022InventoryAuthority

dird17 : DIRDInventoryEntry
dird17 = dird-entry 17 "Maverick Inventor Versus Corporate Inventor - Where Will the Next Major Innovations Arise?" 19 inventoryTitleOnly dia2022InventoryAuthority

dird18 : DIRDInventoryEntry
dird18 = dird-entry 18 "Traversible Wormholes, Stargates, and Negative Energy" 42 releasedReportInspected dia2022InventoryAuthority

dird19 : DIRDInventoryEntry
dird19 = dird-entry 19 "Antigravity for Aerospace Applications" 44 releasedReportInspected dia2022InventoryAuthority

dird20 : DIRDInventoryEntry
dird20 = dird-entry 20 "Biosensors and BioMEMS - A Survey of the Present Field" 45 inventoryTitleOnly dia2022InventoryAuthority

dird21 : DIRDInventoryEntry
dird21 = dird-entry 21 "High-Frequency Gravitational Wave Communications" 57 inventoryTitleOnly dia2022InventoryAuthority

dird22 : DIRDInventoryEntry
dird22 = dird-entry 22 "Metamaterials for Aerospace Applications" 38 inventoryTitleOnly dia2022InventoryAuthority

dird23 : DIRDInventoryEntry
dird23 = dird-entry 23 "State of the Art and Evolution of High-Energy Laser Weapons" 31 inventoryTitleOnly dia2022InventoryAuthority

dird24 : DIRDInventoryEntry
dird24 = dird-entry 24 "Concepts for Extracting Energy From the Quantum Vacuum" 57 inventoryTitleOnly dia2022InventoryAuthority

dird25 : DIRDInventoryEntry
dird25 = dird-entry 25 "An Introduction to the Statistical Drake Equation" 55 inventoryTitleOnly dia2022InventoryAuthority

dird26 : DIRDInventoryEntry
dird26 = dird-entry 26 "Anomalous Acute and Subacute Field Effects on Human Biological Tissues" 38 inventoryTitleOnly dia2022InventoryAuthority

dird27 : DIRDInventoryEntry
dird27 = dird-entry 27 "Laser Lightcraft Nanosatellites" 77 inventoryTitleOnly dia2022InventoryAuthority

dird28 : DIRDInventoryEntry
dird28 = dird-entry 28 "Cockpits in the Era of Breakthrough Flight" 57 inventoryTitleOnly dia2022InventoryAuthority

dird29 : DIRDInventoryEntry
dird29 = dird-entry 29 "Negative Mass Propulsion" 43 inventoryTitleOnly dia2022InventoryAuthority

dird30 : DIRDInventoryEntry
dird30 = dird-entry 30 "Aneutronic Fusion Propulson" 50 inventoryTitleOnly dia2022InventoryAuthority

dird31 : DIRDInventoryEntry
dird31 = dird-entry 31 "Detection and High Resolution Tracking of Vehicles at Hypersonic Velocities" 46 inventoryTitleOnly dia2022InventoryAuthority

dird32 : DIRDInventoryEntry
dird32 = dird-entry 32 "Ultracapacitators as Energy and Power Storage Devices" 34 inventoryTitleOnly dia2022InventoryAuthority

dird33 : DIRDInventoryEntry
dird33 = dird-entry 33 "MHD Air Breathing Propulsion and Power for Aerospace Applications" 32 inventoryTitleOnly dia2022InventoryAuthority

dird34 : DIRDInventoryEntry
dird34 = dird-entry 34 "Cognitive Limits on Simultaneous Control of Multiple Unmanned Spacecraft" 31 inventoryTitleOnly dia2022InventoryAuthority

dird35 : DIRDInventoryEntry
dird35 = dird-entry 35 "Quantum Computing and Utilizing Organic Molecules in Automation Technology" 54 inventoryTitleOnly dia2022InventoryAuthority

dird36 : DIRDInventoryEntry
dird36 = dird-entry 36 "Quantum Tomography of Negative Energy States in the Vacuum" 51 inventoryTitleOnly dia2022InventoryAuthority

dird37 : DIRDInventoryEntry
dird37 = dird-entry 37 "Aneutronic Fusion Propulsion II" 36 inventoryTitleOnly dia2022InventoryAuthority

diaInventory37 : List DIRDInventoryEntry
diaInventory37 =
  dird01 ∷
  dird02 ∷
  dird03 ∷
  dird04 ∷
  dird05 ∷
  dird06 ∷
  dird07 ∷
  dird08 ∷
  dird09 ∷
  dird10 ∷
  dird11 ∷
  dird12 ∷
  dird13 ∷
  dird14 ∷
  dird15 ∷
  dird16 ∷
  dird17 ∷
  dird18 ∷
  dird19 ∷
  dird20 ∷
  dird21 ∷
  dird22 ∷
  dird23 ∷
  dird24 ∷
  dird25 ∷
  dird26 ∷
  dird27 ∷
  dird28 ∷
  dird29 ∷
  dird30 ∷
  dird31 ∷
  dird32 ∷
  dird33 ∷
  dird34 ∷
  dird35 ∷
  dird36 ∷
  dird37 ∷ []

inventorySize : List DIRDInventoryEntry → Nat
inventorySize [] = zero
inventorySize (_ ∷ entries) = suc (inventorySize entries)

inventoryListedPages : List DIRDInventoryEntry → Nat
inventoryListedPages [] = zero
inventoryListedPages (entry ∷ entries) =
  listedPages entry + inventoryListedPages entries

inspectedSize : List DIRDInventoryEntry → Nat
inspectedSize [] = zero
inspectedSize (dird-entry _ _ _ inventoryTitleOnly _ ∷ entries) =
  inspectedSize entries
inspectedSize (dird-entry _ _ _ releasedReportInspected _ ∷ entries) =
  suc (inspectedSize entries)

exactInventoryCount : inventorySize diaInventory37 ≡ 37
exactInventoryCount = refl

exactInventoryListedPageTotal : inventoryListedPages diaInventory37 ≡ 1473
exactInventoryListedPageTotal = refl

onlyFourOriginalReportsInspected : inspectedSize diaInventory37 ≡ 4
onlyFourOriginalReportsInspected = refl

-- Exact source list and independently inspected report bodies are separate:
diaWarpBody : Inspected.PrimaryDocumentReading
diaWarpBody = Inspected.diaWarp

diaVacuumBody : Inspected.PrimaryDocumentReading
diaVacuumBody = Inspected.diaVacuum

diaWormholesBody : Inspected.PrimaryDocumentReading
diaWormholesBody = Inspected.diaWormholes

diaAntigravityBody : Inspected.PrimaryDocumentReading
diaAntigravityBody = Inspected.diaAntigravity

data DirdTitleEstablishesOperation : Set where
data FourInspectionsConstituteThirtySevenFullReadings : Set where
data ThirtySevenEqualsNarratedThirtyEight : Set where

noTitleToDeviceProof : DirdTitleEstablishesOperation → ⊥
noTitleToDeviceProof ()
noFourToFullInspection : FourInspectionsConstituteThirtySevenFullReadings → ⊥
noFourToFullInspection ()
noNarratorCountPromotion : ThirtySevenEqualsNarratedThirtyEight → ⊥
noNarratorCountPromotion ()
