module DASHI.Biology.QuailEggHistamineGutSnowballRegression where

open import DASHI.Core.Prelude using (⊥)

import DASHI.Biology.QuailEggHistamineGutSnowballExact as Q

quailCellEvidenceRegression : Q.QuailEggMastCellEvidenceReceipt
quailCellEvidenceRegression = Q.lianto2018QuailEggReceipt

ovomucoidEvidenceRegression : Q.QuailOvomucoidEvidenceReceipt
ovomucoidEvidenceRegression = Q.quailOvomucoid2023Receipt

microbialHistamineRegression : Q.IBSMicrobialHistamineReceipt
microbialHistamineRegression = Q.dePalma2022IBSHistamineReceipt

serumDAONotGutDAORegression : Q.SerumDAOEqualsGutDAOPermission → ⊥
serumDAONotGutDAORegression = Q.serumDAODoesNotEqualGutDAO

quailNotIBSTreatmentRegression : Q.QuailEggTreatsIBSPermission → ⊥
quailNotIBSTreatmentRegression = Q.quailEggEvidenceDoesNotPayIBSTreatment

canonicalBoundaryRegression : Q.QuailEggHistamineGutBoundary
canonicalBoundaryRegression = Q.canonicalQuailEggHistamineGutBoundary
