#!/usr/bin/env python3
"""Deterministic broad visual proof for the epistemic-authority specimen.

The generator deliberately keeps relation kinds explicit.  The first hand-made
broad draft used ordinary arrows too aggressively and visually suggested false
sequential derivations.  This version makes shared-input evaluation, authority
profile transition, epistemic refinement, and capability inclusion distinct in
layout and labels.
"""
from pathlib import Path

W, H = 1500, 1120
OUT = Path("artifacts/introspective/epistemic-authority/epistemic_authority_broad_visual_proof.svg")

PANELS = [
    (40, 105, 690, 260, "1. Capture is a change of authority profile"),
    (770, 105, 690, 260, "2. Same fine states, different observers"),
    (40, 395, 690, 270, "3. Go-like opacity: public rules do not determine lay evaluation"),
    (770, 395, 690, 270, "4. Objective imputation != actual comprehension"),
    (40, 695, 690, 320, "5. Learned anchors shape the subjective Pareto frontier"),
    (770, 695, 690, 320, "6. AI actuation can expand while observation stays coarse"),
]


def esc(text: str) -> str:
    return (text.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;"))


def rect(x, y, w, h, cls="node"):
    return f'<rect x="{x}" y="{y}" width="{w}" height="{h}" class="{cls}"/>'


def text(x, y, value, cls="label"):
    return f'<text x="{x}" y="{y}" class="{cls}">{esc(value)}</text>'


def line(x1, y1, x2, y2, cls="line"):
    return f'<path d="M{x1} {y1} L{x2} {y2}" class="{cls}"/>'


def node(x, y, w, h, label, cls="node", sub=None):
    out = [rect(x, y, w, h, cls), text(x + 18, y + 33, label)]
    if sub:
        out.append(text(x + 18, y + 55, sub, "small"))
    return out


def build():
    s = [f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">']
    s += ["""<style>
text{font-family:DejaVu Sans,sans-serif;fill:#111}.title{font-size:30px;font-weight:700}.paneltitle{font-size:21px;font-weight:700}.label{font-size:17px}.small{font-size:14px}.node{fill:#fff;stroke:#111;stroke-width:2.5;rx:14}.folk{fill:#f5f5f5;stroke:#111;stroke-width:2.5;rx:14}.inst{fill:#e9eef5;stroke:#111;stroke-width:2.5;rx:14}.accent{fill:#eef7ee;stroke:#111;stroke-width:2.5;rx:14}.warn{fill:#fff3e8;stroke:#111;stroke-width:2.5;rx:14}.line{stroke:#111;stroke-width:3;fill:none;marker-end:url(#arrow)}.thin{stroke:#555;stroke-width:2;fill:none;marker-end:url(#arrow)}.dash{stroke:#555;stroke-width:2.5;fill:none;stroke-dasharray:8 7;marker-end:url(#arrow)}.trade{stroke:#555;stroke-width:2.5;fill:none}</style>
<defs><marker id="arrow" markerWidth="10" markerHeight="10" refX="8" refY="3" orient="auto" markerUnits="strokeWidth"><path d="M0,0 L0,6 L9,3 z" fill="#111"/></marker></defs>"""]
    s += [text(50, 48, "Epistemic authority capture: refined visual proof", "title"),
          text(50, 78, "Formal theory -> visual observer -> direct inspection -> refined formal result", "small")]
    for x, y, w, h, title in PANELS:
        s += [rect(x, y, w, h), text(x + 25, y + 32, title, "paneltitle")]

    s += [text(85, 165, "BEFORE: within-community", "small")]
    s += node(70, 185, 180, 55, "Norm memory: community", "accent")
    s += node(275, 185, 180, 55, "Evaluation: community", "accent")
    s += node(480, 185, 190, 55, "Binding meaning: community", "accent")
    s += [line(370, 245, 370, 282), text(390, 270, "institutional differentiation", "small")]
    s += [text(85, 302, "AFTER: publication can coexist with captured evaluation", "small")]
    s += node(70, 315, 180, 40, "Norm memory: community", "accent")
    s += node(275, 315, 180, 40, "Evaluation: institution", "inst")
    s += node(480, 315, 190, 40, "Binding meaning: institution", "inst")

    s += node(800, 185, 160, 55, "viable state")
    s += node(800, 275, 160, 55, "no-prospect state")
    s += node(1030, 220, 155, 65, "looks eligible", "folk")
    s += [f'<path d="M960 212 C1000 212 1005 235 1030 242" class="dash"/>',
          f'<path d="M960 302 C1000 302 1005 270 1030 262" class="dash"/>']
    s += node(1250, 180, 165, 55, "institution: viable", "inst")
    s += node(1250, 275, 165, 55, "institution: no prospect", "inst")
    s += [line(960, 212, 1250, 207, "thin"), line(960, 302, 1250, 302, "thin"),
          text(805, 350, "The folk fibre contains two institutionally distinct fine states.", "small")]

    s += node(70, 470, 150, 55, "Public rules", "accent")
    s += node(70, 555, 150, 55, "Fine position")
    s += node(300, 455, 180, 70, "Folk evaluator", "folk", "coarse / collision")
    s += node(300, 550, 180, 70, "Institutional evaluator", "inst", "refined / separating")
    for a, b, c, d in [(220,495,300,485),(220,495,300,570),(220,580,300,500),(220,580,300,585)]:
        s += [line(a,b,c,d,"thin")]
    s += node(550, 455, 145, 70, "same folk result", "folk", "for both states")
    s += node(550, 550, 145, 70, "distinct outcomes", "inst", "institutional")
    s += [line(480,490,550,490), line(480,585,550,585),
          text(80, 642, "No folk -> institution derivation: both evaluate the shared inputs.", "small")]

    s += node(800, 500, 140, 55, "received")
    s += node(1000, 455, 185, 55, "reasonably apparent", "warn")
    s += node(1240, 455, 160, 55, "persist", "warn")
    s += [line(940,520,1000,482), line(1185,482,1240,482), text(1200,443,"objective gateway","small")]
    s += node(1000, 560, 185, 55, "comprehended", "accent")
    s += node(1240, 560, 160, 55, "withdraw", "accent")
    s += [line(940,535,1000,587), line(1185,587,1240,587),
          text(800,642,"Teach-back adds an observer; receipt/apparentness does not certify comprehension.","small")]

    s += [text(80,760,"BEFORE refinement","small")]
    s += node(70,780,190,80,"folk model","folk","anchor fit up; evidence fit down")
    s += node(315,780,210,80,"institutional model","inst","anchor fit down; evidence fit up")
    s += [line(260,820,315,820,"trade"), text(264,805,"trade-off","small")]
    s += node(130,895,340,55,"verified explanation / observer refinement","accent")
    s += [line(300,950,300,978), text(340,980,"AFTER: a missing distinction becomes visible;","small"),
          text(340,999,"the folk model can leave the feasible set.","small")]

    s += node(800,785,180,70,"coarse observer","folk","unchanged")
    s += node(1040,755,200,70,"baseline action set","node","plain, withdraw")
    s += node(1040,855,200,70,"AI-expanded action set","warn","plain, ornate, withdraw")
    s += [line(980,815,1040,790,"thin"), line(980,825,1040,890,"thin")]
    s += node(1290,815,140,70,"possible impact","inst","can increase")
    s += [line(1240,890,1290,855), text(805,965,"Capability can increase without observer refinement.","small"),
          text(805,988,"Non-claim: a larger action set lowers ideal optimal utility.","small")]

    s += [text(45,1070,"Typed visual relations: authority-profile transition | shared-input computation | epistemic refinement | capability inclusion", "small"), "</svg>"]
    return "\n".join(s)


def main():
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(build(), encoding="utf-8")
    print(OUT)


if __name__ == "__main__":
    main()
