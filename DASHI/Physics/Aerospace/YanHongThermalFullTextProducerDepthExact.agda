module DASHI.Physics.Aerospace.YanHongThermalFullTextProducerDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record YanThermalFullTextProducerDepth : Set where
  constructor yan-thermal-fulltext-producer-depth
  field
    sourceReference : String
    fullTextHTMLVisible : Bool
    fourCasesVisible : Bool
    machNumberVisible : Bool
    governingEquationFamilyVisible : Bool
    downloadableArticleAdvertised : Bool
    machineReadableFiguresVisible : Bool
    machineReadableTablesVisible : Bool
    exactShockAngleSeriesVisible : Bool
    exactSeparationSeriesVisible : Bool
    nextProducerLeaf : String

open YanThermalFullTextProducerDepth public

yanThermalFullTextProducerDepth : YanThermalFullTextProducerDepth
yanThermalFullTextProducerDepth = yan-thermal-fulltext-producer-depth
  "DOI 10.7638/kqdlxxb-2013.0102"
  true
  true
  true
  true
  true
  false
  false
  false
  false
  "acquire/download article figures or underlying response series, then bind geometry/mesh/boundary conditions and shock/separation outputs"

fullTextPaysCaseTopology : Bool
fullTextPaysCaseTopology = true

fullTextPaysResponseArrays : Bool
fullTextPaysResponseArrays = false

fullTextPaysVehicleDesign : Bool
fullTextPaysVehicleDesign = false
