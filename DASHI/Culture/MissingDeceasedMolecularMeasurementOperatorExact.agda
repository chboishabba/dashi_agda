module DASHI.Culture.MissingDeceasedMolecularMeasurementOperatorExact where

open import DASHI.Core.Prelude
open import DASHI.Core.ScientificOperatorFamilyExact as O

maiwaldMolecularMeasurement : O.OperatorFactorisation
maiwaldMolecularMeasurement = O.operator-factorisation
  "Frank W. Maiwald"
  "DASHI.Physics.Spectroscopy.MaiwaldActionSpectroscopyBidiExact"
  O.molecularMeasurementShape
  "tagged molecular ion + IR excitation -> photodissociation fragments/action spectrum -> conformer inference"
  "Measurement/calibration and molecular-structure inference remain distinct from other biochemical assay mechanisms."

thomasMolecularMeasurement : O.OperatorFactorisation
thomasMolecularMeasurement = O.operator-factorisation
  "Jason R. Thomas"
  "DASHI.Biology.JasonThomasSignallingBidiExact"
  O.molecularMeasurementShape
  "chemical perturbation + assay readout -> target/signalling response -> validated target/pathway inference"
  "Perturbation-to-readout shares molecular measurement geometry; direct-target validation remains mandatory."

liMinyongMolecularMeasurement : O.OperatorFactorisation
liMinyongMolecularMeasurement = O.operator-factorisation
  "Li Minyong"
  "DASHI.Biology.LiMinyongPhotopharmacologyBidiExact"
  O.molecularMeasurementShape
  "photoswitch/probe + wavelength -> molecular state/binding -> optical or physiological readout"
  "Photochemical controllability shares molecular-state/readout structure; compound-specific kinetics remain separate."

molecularMeasurementFactorisations : List O.OperatorFactorisation
molecularMeasurementFactorisations =
  maiwaldMolecularMeasurement ∷ thomasMolecularMeasurement ∷ liMinyongMolecularMeasurement ∷ []
