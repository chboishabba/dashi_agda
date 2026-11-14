module DASHI.Biology.IBSHistamineH1InterventionUpdateRegression where

import DASHI.Biology.IBSHistamineH1InterventionUpdateExact as H

phase2Regression : H.H1InterventionReceipt
phase2Regression = H.decraecker2024Receipt

doseRegression : H.H1InterventionReceipt
doseRegression = H.pia2026Receipt

boundaryRegression : H.IBSHistamineH1InterventionBoundary
boundaryRegression = H.canonicalIBSHistamineH1InterventionBoundary
