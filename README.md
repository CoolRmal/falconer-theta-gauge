# Falconer's distance problem for logarithmic gauges

Lean 4 / Mathlib project for Theorem 1.1 in the
[source manuscript](docs/falconer-theta-gauge-proof.pdf), dated October 8, 2026.

**Status: work in progress. The main theorem is not proved, does not pass
Comparator, and is not registered on Palomar.**

For

$$
\frac23 < \theta < 1,\qquad
h_\theta(r)=r\exp\!\left(-\bigl(\log(1/r)\bigr)^\theta\right)
\quad (0<r<1),\qquad h_\theta(0)=0,
$$

Theorem 1.1 states that a compact set in the Euclidean plane satisfies

$$
\mathcal H^{h_\theta}(E)>0
\quad\Longrightarrow\quad
\mathcal L^1\bigl(\Delta(E)\bigr)>0,
\qquad
\Delta(E)=\{\lVert x-y\rVert:x,y\in E\}.
$$

`gaugeMeasure` uses Mathlib's arbitrary-gauge Hausdorff measure
`MeasureTheory.Measure.mkMetric`. The gauge is extended by the identity at
radii at least one; its prescribed small-radius values are exact.
`Plane` is `EuclideanSpace ℝ (Fin 2)`, and `volume` on the real line is Lebesgue
measure. The distance set of compact `E` is proved compact and measurable.

The independent [Challenge](Challenge.lean) imports only Mathlib and repeats
every custom statement definition. [Solution](Solution.lean) imports the
development without importing Challenge. The target retains the manuscript's
exact hypotheses; no Frostman, radial projection, or energy estimate is added
as a hypothesis.

The proved foundation includes gauge positivity, comparison with the linear
gauge, compactness and measurability of the distance set, the positive
branch-counting exponent above two thirds, logarithmic domination by powers,
summability of stretched exponentials and the modeled filter-error power,
the exact rounded parameters from Definition 2.1, positive gauge content,
and finite dyadic gauge weights with saturated covering bounds. Lemma 5.1's
full gauge Frostman probability measure and its finite logarithmic critical
energies are now proved. The actual rounded filter error is summable.

The summable reconstruction foundation proves that dyadic frequency shells
overlap at most three times, obtains the finite-overlap quadratic L² bound,
and proves convergence of square-summable shell pieces and summable errors.
Actual smooth Fourier cutoffs, uniformly integrable convolution errors, and
low-pass convergence on Schwartz tests are proved, as is the final absolute
continuity consequence of an L¹ plus Fourier L² pairing. The remaining series
identification in the full reconstruction criterion is in progress.

The [formalization notebook](docs/output/formalization-notebook.pdf) explains
the geometric, scalar, Frostman, and reconstruction foundations. Its [Markdown source](docs/formalization-notebook.md)
uses GitHub display-math delimiters.

The unresolved proof is in [Main](FalconerThetaGauge/Main.lean). Its deliberate
proof hole is rejected by Comparator because `sorryAx` is not permitted.
The separate hole in Challenge records the independent specification.

## Build and verification

The project pins Lean `4.35.0-rc2` and Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

```sh
lake exe cache get
lake build FalconerThetaGauge Challenge Solution
```

The [GitHub workflow](.github/workflows/verify.yml) has separate build and
Comparator jobs on every push and pull request. A successful build of a proof
skeleton is not a successful proof verification. Comparator compares the
complete statement and definition dependencies, enforces the three standard
axioms, and checks the exported proof with Lean, NanoDa, and con-ron.

```sh
./scripts/verify-comparator.sh
```

The normal check requires Linux and Bubblewrap. On a trusted local macOS
development checkout, `./scripts/verify-comparator.sh --preliminary` runs a
comparison with the sandbox disabled and explicitly refuses execution in CI.
Such a run is not a Palomar mechanical report.

## Completion and Palomar

The remaining work includes logarithmically weighted Fourier and projection
energies, the endpoint Orlicz radial estimate,
the summable reconstruction criterion, quantitative regular decomposition,
the four uniform energy estimates, and the budget induction and final assembly.
The fixed-parameter packing development does not establish these estimates
when the parameters shrink with the terminal scale.

After the target is proved without holes, the exact public commit must pass
the Comparator job and the full pinned Palomar mechanical preflight. Complete
truthful `formalization.yaml` metadata and obtain the registry's review before
registration through [Palomar's submission protocol](https://palomar-registry.org/how-to-submit).
The manual GitHub workflow includes the full preflight; submission and
registration are separate actions.
