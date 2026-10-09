# Falconer's distance problem for logarithmic gauges

A Lean 4 / Mathlib formalization of Theorem 1.1 in the
[October 8, 2026 manuscript](docs/falconer-theta-gauge-proof.pdf).
The theorem is proved without proof holes or additional analytic assumptions.
Palomar registration is pending.

For $\frac{2}{3}\lt\theta\lt1$, define $h_\theta(0)=0$ and

$$h_\theta(r)=r\exp\left(-\bigl(\log(1/r)\bigr)^\theta\right)\qquad(0\lt r\lt1).$$

For a compact set $E\subset\mathbb{R}^2$, let

$$\Delta(E)=\lbrace\lVert x-y\rVert:x,y\in E\rbrace.$$

Then

$$\mathcal{H}^{h_\theta}(E)>0\quad\Longrightarrow\quad\mathcal{L}^1\bigl(\Delta(E)\bigr)>0.$$

The plane has the Euclidean metric. Gauge Hausdorff measure uses Mathlib's
`Measure.mkMetric`, with covering diameters; extending the gauge by the identity
for radii at least one does not change this measure. The conclusion uses ordinary
Lebesgue measure on the real line.

- [Challenge](Challenge.lean): the independent statement, importing only Mathlib.
- [Main theorem](FalconerThetaGauge/Main.lean): `FalconerThetaGauge.theorem_one_one`.
- [Proof notebook (PDF)](docs/output/formalization-notebook.pdf): the proof structure
  and detailed correspondence with the manuscript.
- [Metadata](formalization.yaml): provenance, automation disclosure, and adaptations
  of intermediate arguments.

## Verification

[GitHub Actions](https://github.com/CoolRmal/falconer-theta-gauge/actions/workflows/verify.yml)
builds the development, audits axiom dependencies, and runs sandboxed Comparator
with **Lean, NanoDa, and con-ron**. The [configuration](comparator.json) fixes all
statement definitions and permits only `propext`, `Quot.sound`, and `Classical.choice`.
The single intentional `sorry` belongs to the independent Challenge; Solution
imports the completed proof and does not import Challenge.

The proof snapshot `98d3222` also passed
[full Palomar mechanical verification](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/37911192794).
[Recorded evidence](docs/verification.json) distinguishes verified snapshots from
historical development failures. Mechanical verification and registry publication
are separate steps.

## Build

Lean `4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` are pinned.

```sh
lake exe cache get
lake build FalconerThetaGauge Challenge Solution
python3 scripts/check-proof-status.py
./scripts/verify-comparator.sh
```

Comparator requires Linux and Bubblewrap. For a trusted local macOS checkout,
`./scripts/verify-comparator.sh --preliminary` runs without the sandbox; this mode
is refused in CI and is not Palomar verification. The workflow's manual run also
provides the full Palomar mechanical preflight.

Author and responsible maintainer: **Yongxi Lin**. License: **Apache-2.0**.
