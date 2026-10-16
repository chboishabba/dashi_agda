module DASHI.Physics.QuantumVacuum.CasimirQuantumInequalityBoundaryValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.QuantumVacuum.CasimirQuantumInequalityBoundaryExact as QI

------------------------------------------------------------------------
-- RED-first regression surface for pointwise/averaged/QI non-collapse.
------------------------------------------------------------------------

fordRoman1995DOIRegression :
  QI.fordRoman1995DOI ≡ "10.1103/PhysRevD.51.4277"
fordRoman1995DOIRegression = refl

fordRoman1997DOIRegression :
  QI.fordRoman1997DOI ≡ "10.1103/PhysRevD.55.2082"
fordRoman1997DOIRegression = refl

pointwiseDoesNotPayANECRegression :
  QI.PointwiseNECViolationAutomaticallyPaysANECViolation → ⊥
pointwiseDoesNotPayANECRegression = QI.pointwiseNECDoesNotPayANEC

citationDoesNotPaySamplingRegression :
  QI.QILiteratureAutomaticallySuppliesCasimirSamplingWitness → ⊥
citationDoesNotPaySamplingRegression = QI.qiLiteratureDoesNotSupplySamplingWitness

backgroundMustRemainExplicitRegression :
  QI.CasimirBackgroundMayBeSilentlyReplacedByMinkowskiVacuum → ⊥
backgroundMustRemainExplicitRegression = QI.casimirBackgroundCannotBeSilentlyReplaced

engineeringNonPromotionRegression :
  QI.QIBoundAutomaticallyLicensesMacroscopicNegativeEnergyEngineering → ⊥
engineeringNonPromotionRegression = QI.qiDoesNotLicenseEngineering
