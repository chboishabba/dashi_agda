module DASHI.Physics.Chemistry.AmmoniaSTO3GFCIValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaSTO3GFCIExact as FCI

nh3HasTenElectrons :
  FCI.NH3STO3GFCIReceipt.electrons FCI.canonicalNH3STO3GFCIReceipt ≡ 10
nh3HasTenElectrons = refl

nh3HasSixteenSpinOrbitals :
  FCI.NH3STO3GFCIReceipt.spinOrbitals FCI.canonicalNH3STO3GFCIReceipt ≡ 16
nh3HasSixteenSpinOrbitals = refl

hfEnergyEncoded :
  FCI.NH3STO3GFCIReceipt.hfEnergyTenThousandthHartree FCI.canonicalNH3STO3GFCIReceipt ≡ 554554
hfEnergyEncoded = refl

fciEnergyEncoded :
  FCI.NH3STO3GFCIReceipt.fciEnergyTenThousandthHartree FCI.canonicalNH3STO3GFCIReceipt ≡ 555245
fciEnergyEncoded = refl

modelDiagonalizationPaid :
  FCI.STO3GFCIBoundary.sourceBackedFCIDiagonalizationPaid
    FCI.canonicalSTO3GFCIBoundary ≡ true
modelDiagonalizationPaid = refl

coefficientsNotImported :
  FCI.STO3GFCIBoundary.literalFCIEigenvectorCoefficientsImported
    FCI.canonicalSTO3GFCIBoundary ≡ false
coefficientsNotImported = refl
