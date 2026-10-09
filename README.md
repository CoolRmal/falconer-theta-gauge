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
All four budget groups of Lemma 2.2 and the weighted Fourier energy estimate
of Lemma 5.2 are proved. The separated probability preparation retains the
specified unit-square geometry, gauge bounds, and finite energies.
Lemma 5.8 is proved for the actual original cell weights: disjoint terminal-cell
carriers retain mass at least `2^(-κN/2)`, discard at most `2·2^(-κN/4)`, and
give normalized probabilities regular at every depth from zero through `N`.
Lemma 5.10's excess-function bounds are proved from actual maximal cell masses
and the original gauge bound, including the exact Lipschitz constant and gain.
Lemma 5.3 is proved, including joint measurable L² densities and the exact
averaged logarithmic Orlicz estimate. The radial development
includes the exact weighted polar identity, its smooth Orlicz transfer, and
absolute continuity of weak limits under uniform logarithmic bounds, with
finite lower Orlicz moments for their actual Radon–Nikodym densities.
The target-specific radial endpoint is assembled using the gauge's finite
energies at every logarithmic order. Compact quarter-mass restrictions give
a common eighth-order radial moment bound at every retained pin in both
directions, proving the spread requirement of Proposition 5.6(c).
The actual pair directions lie in one closed arc of length at most 1/20,
completing the common-arc geometry of Proposition 5.6(b).
Actual occupied-descendant counts, entry-depth bounds, split budget gains,
and finite scheduled test lists with at most `N²` tests are also proved.
The nonstationary and linear phase bounds have explicit constants, including
the periodic version. For each finite derivative order, a genuine smooth even
probability bump has the required factorial L¹ derivative estimates.
Literal tube and projection tests now have their exact Markov bounds and
jointly measurable smooth masks. The weighted distance measure, finite-test
filters, actual regular-carrier loss, and summability of removed mass are
proved for the actual filters on all retained regular pieces. Directional
widening and the exact tube/projection average estimates of Lemma 6.5 are proved. Actual move chains and induction trees, including repeated paths,
satisfy the length, cost, multiplier, and node-count budgets. Scalar binning
estimates (7.3(i)--(iv)) are proved for actual finite measures, including
the literal angular Fourier comparisons with constants 2 and 160.
Quadratic stationary phase is proved for Schwartz and smooth compact
amplitudes in both signs, with the exact prefactor and remainder. The actual
arcsine substitution and localized circle expansion are proved, with actual
uniform amplitude derivative bounds and the operator budget `(100 j M²)^j`.
Literal inverse operators have proved degree, cancellation and numerical
norm bounds, with actual finite-order action costs. The full periodic circular
expansion for smooth amplitudes has the source remainder constant; finite
inversion has a proved geometric tail bound. The literal prepared-arc cutoff
has its exact support and derivative budgets. Actual masked Fourier and
distance energies satisfy the source trivial and reached-mask bounds. The
weighted distance Fourier transform and a genuine low/high dyadic bridge are
proved, including the literal next-level mask sandwich and Lemma 7.4 with
constant 320. The actual scheduled symbol class now has a finite derivative expansion,
coefficient budget, reached-factor energy contraction, and actual state-energy
maxima. Prepared one-sided circular inversion has its correct complex constant
and a proved terminal error for these actual symbols. The spatial inverse-power
series is genuinely separable with bounded polynomial factors and summable
coefficients. Finite and countable circular Cauchy–Schwarz estimates control the
actual bilinear integrals by the actual masked energies. Equal-arc convolutions,
finite Schur bounds, and pointwise phase separation for unlinked cells are
proved. Estimate 7.7 is complete for the actual weighted distance energies.
The full inverse-circle Fourier series has a proved coefficient bound 11/10.
The genuine nonzero-symbol linking graph has degree at most `R^(height+12ε)`,
and actual angular and radial integrals satisfy the source decay bounds.
Their final joint Fourier-energy assembly and the full space split remain.

The summable reconstruction foundation proves that dyadic frequency shells
overlap at most three times, obtains the finite-overlap quadratic L² bound,
and proves convergence of square-summable shell pieces and summable errors.
Actual smooth Fourier cutoffs, uniformly integrable convolution errors, and
low-pass convergence on Schwartz tests are proved, as is the final absolute
continuity consequence of an L¹ plus Fourier L² pairing. The series
identification is complete, proving the full summable reconstruction criterion
of Lemma 4.2 with its exact dominated-measure and shell-energy hypotheses.

The [formalization notebook](docs/output/formalization-notebook.pdf) explains
the geometric, scalar, Frostman, and reconstruction foundations. Its [Markdown source](docs/formalization-notebook.md)
uses GitHub display-math delimiters.

The unresolved proof is in [Main](FalconerThetaGauge/Main.lean). It uses the
proved preparation and weighted distance carrier; its sole proof hole is
absolute continuity of that actual weighted distance measure. Comparator
rejects this hole because `sorryAx` is not permitted.
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

The remaining work includes completing Estimates 7.5, 7.6 and 7.8, then
assembling the actual induction and the final frequency shells. Estimate 7.7
is proved. The actual terminal-tree contributions and accumulated small
errors already satisfy their budget bounds.
The fixed-parameter packing development does not establish these estimates
when the parameters shrink with the terminal scale.

After the target is proved without holes, the exact public commit must pass
the Comparator job and the full pinned Palomar mechanical preflight. Complete
truthful `formalization.yaml` metadata and obtain the registry's review before
registration through [Palomar's submission protocol](https://palomar-registry.org/how-to-submit).
The manual GitHub workflow includes the full preflight; submission and
registration are separate actions.
