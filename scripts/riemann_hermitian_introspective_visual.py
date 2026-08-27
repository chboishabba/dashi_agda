#!/usr/bin/env python3
"""Deterministic visual observer for the 2026 Hermitian zeta route.

This is deliberately not a proof authority.  It renders exact algebra already
owned by the Agda tranche so that geometric/representational consequences can
be inspected and then proved back in Agda.

Rendered identities:

  B_full = 2(B_fin + B_tail)
  B_fin  = B_tail + M

  Im S = q+r
  Im H = r-q
  (Im S)^2 + (Im H)^2 = 2(q^2+r^2)

  C+D=A, A+s_t=G+E_t, G+s_p=C+E_p

The first introspective round-trip recovered:

  B_full + 2M = 4 B_fin
  Im S - Im H = 2q
  Im S + Im H = 2r

Those recovered statements are re-proved in
DASHI.Analysis.RiemannHermitianIntrospectiveRoundTripExact.
"""

from pathlib import Path


def esc(s: str) -> str:
    return (s.replace("&", "&amp;").replace("<", "&lt;")
             .replace(">", "&gt;"))


def text(x, y, s, size=18, weight="normal", anchor="start"):
    return (
        f'<text x="{x}" y="{y}" font-family="sans-serif" '
        f'font-size="{size}" font-weight="{weight}" text-anchor="{anchor}">'
        f'{esc(s)}</text>'
    )


def rect(x, y, w, h, dash=""):
    extra = f' stroke-dasharray="{dash}"' if dash else ""
    return f'<rect x="{x}" y="{y}" width="{w}" height="{h}" fill="none" stroke="currentColor" stroke-width="2"{extra}/>'


def line(x1, y1, x2, y2, width=2):
    return f'<line x1="{x1}" y1="{y1}" x2="{x2}" y2="{y2}" stroke="currentColor" stroke-width="{width}"/>'


def main() -> None:
    out = Path(__file__).resolve().parents[1] / "Docs" / "support" / "reference" / "RiemannHermitianIntrospectiveVisualProof.svg"
    out.parent.mkdir(parents=True, exist_ok=True)

    s = []
    s.append('<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 1400 960" color="#111">')
    s.append('<rect width="1400" height="960" fill="white"/>')
    s.append(text(700, 45, "Hermitian defect route — deterministic visual proof", 28, "bold", "middle"))

    # Panel A
    s.append(rect(40, 80, 640, 380))
    s.append(text(60, 120, "A. Centered source-grid retention", 22, "bold"))
    gy = 245
    s.append(line(105, gy, 620, gy))
    for j, k in enumerate(range(-4, 5)):
        x = 125 + 58 * j
        s.append(line(x, gy - 22, x, gy + 22))
        s.append(text(x, gy + 48, str(k), 13, anchor="middle"))
    s.append(text(357, gy - 48, "tau_0 = gamma", 17, anchor="middle"))
    s.append(text(95, 330, "B_full = 2(B_fin + B_tail)", 18))
    s.append(text(95, 365, "B_fin = B_tail + M", 18))
    s.append(rect(335, 310, 300, 85))
    s.append(text(485, 342, "Recovered visual identity", 16, "bold", "middle"))
    s.append(text(485, 374, "B_full + 2M = 4 B_fin", 19, anchor="middle"))
    s.append(text(95, 425, "=> full transverse energy <= 4 × finite one-sided energy", 16))

    # Panel B
    s.append(rect(720, 80, 640, 380))
    s.append(text(740, 120, "B. S/H channels are a Hadamard transform", 22, "bold"))
    cx, cy = 1040, 270
    s.append(line(820, cy, 1260, cy))
    s.append(line(cx, 145, cx, 400))
    s.append(line(cx - 155, cy + 155, cx + 155, cy - 155))
    s.append(line(cx - 155, cy - 155, cx + 155, cy + 155))
    s.append(text(1210, 180, "Im S = q+r", 17, anchor="middle"))
    s.append(text(870, 180, "Im H = r-q", 17, anchor="middle"))
    s.append(text(760, 350, "(Im S)^2 + (Im H)^2 = 2(q^2+r^2)", 18))
    s.append(text(760, 385, "Recovered inverse: Im S - Im H = 2q", 17))
    s.append(text(760, 417, "Recovered inverse: Im S + Im H = 2r", 17))

    # Panel C
    s.append(rect(40, 500, 1320, 410))
    s.append(text(60, 540, "C. Source-native G3 cancellation", 22, "bold"))
    s.append(text(75, 585, "Implemented: C+D=A,   A+s_t=G+E_t,   G+s_p=C+E_p", 19))
    boxes = [(90, 630, "C + D", "finite zero-side A"),
             (470, 630, "G + E_t", "tail transport"),
             (850, 630, "C + E_p", "prime trace")]
    for x, y, top, sub in boxes:
        s.append(rect(x, y, 260, 92))
        s.append(text(x + 130, y + 38, top, 22, anchor="middle"))
        s.append(text(x + 130, y + 70, sub, 14, anchor="middle"))
    s.append(line(350, 676, 470, 676))
    s.append(line(730, 676, 850, 676))
    s.append(text(700, 780, "Cancel the common baseline C", 18, "bold", "middle"))
    s.append(rect(470, 805, 460, 65))
    s.append(text(700, 847, "D + (s_t+s_p) = E_t+E_p", 23, anchor="middle"))
    s.append(text(700, 895, "Only defect D survives; the error floor is tail + prime error.", 16, anchor="middle"))

    s.append('</svg>')
    out.write_text("\n".join(s), encoding="utf-8")
    print(out)


if __name__ == "__main__":
    main()
