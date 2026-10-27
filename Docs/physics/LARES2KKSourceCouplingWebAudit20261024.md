# Earth-source and physical-matter coupling max-cut (2026-10-24)

## New web-grounded correction

Ciufolini et al. *Nature* **655** (2026) 332–335 DOI 10.1038/s41586-026-10715-0: LARES-2/LAGEOS/GRACE frame-dragging estimate at ~one part per thousand. Their explicit Chern–Simons exclusion illustration concerns |Omega_CS/Omega_GR| approximately <= 0.002, NOT a generic KK bound. ILRS separately reports uncertainty around 0.2%; do not conflate publication's nominal error descriptions.

Peng Xu and Yongge Ma, *Physics Letters B* **656** (2007) 165–168, DOI 10.1016/j.physletb.2007.09.035, study a specified reduced five-dimensional metric theory and report a PPN gamma mismatch (half the 4D GR value) under their reduction/matter assumptions. This result is not universally applicable to every KK reduction and matter frame.

## Source/matter frame explicitly tested
Use existing PR #1241 boosted-Kerr quotient. For seed M, q=sinh²(alpha), x=1/r, H=1+2Mqx, F=1-2Mx, Einstein-frame static potentials g_tt=-F/sqrt(H), g_rr=sqrt(H)/F. Both asymptotic 1/r coefficients have magnitude M(2+q), hence weak-field gamma=1 **for the assumed neutral Einstein-frame matter coupling**. The scalar/radion H has nonzero 1/r charge 2Mq when q !=0. A family of alternative physical conformal metrics g_phys=H^beta g_E produces gamma=(2+q+2beta q)/(2+q-2beta q) in this asymptotic radial-coordinate calculation. This is a coupling sensitivity test, not a proposed physical parameter or a full PPN transformation of an interior-joined Earth.

Source matching requires a physically specified five-dimensional stress-energy, rotating compact Earth interior (or justified effective 4D EMD matter action), exact junction conditions, scalar/electric charge matching and a chosen satellite matter coupling. Zero boost q=0 embeds ordinary Kerr product and cannot be constrained as a distinct KK prediction from nodal observations. Boosted charged black strings are not realistic terrestrial material bodies.

## Acceptance
python3 scripts/check_kk_source_matching_gate.py

Mathematical checks: asymptotic symbolic algebra, no kernel/typecheck certification. Empirical claims remain blocked. Do not use SensibLaw/SLR, PNF or W3.
