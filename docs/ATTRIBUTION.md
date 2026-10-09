# Attribution

This project uses Lean and the pinned Mathlib dependency under their respective
licenses. The informal source is the supplied manuscript in
`falconer-theta-gauge-proof.pdf`; no manuscript authorship is inferred from
the separately confirmed formalization author and maintainer.

Several foundations adapt proved code from Yongxi Lin's Apache-2.0
[Falconer packing project](https://github.com/CoolRmal/falconer-packing/tree/70140ccedfb6de71342299523a21b1550df69ab9),
at commit `70140ccedfb6de71342299523a21b1550df69ab9`:

| This development | Original modules |
| --- | --- |
| Gauge Frostman dyadic geometry and weak compactness | `Dyadic`, `FrostmanWeights`, `WeakLimit` |
| Separated normalized measures | `Extraction`, `Restriction` |
| Smooth-cutoff absolute continuity | `SchwartzDensityCriterion`, `WeakDensityLimit` |
| Convolution estimates and low-pass approximation | `SchwartzMeasureReconstruction` |
| Measure Fourier identities and L² pairing | `FourierDensity` |
| Gaussian Fourier duality | `GaussianEnergy` |

Original copyright and author notices are retained in adapted modules.
The gauge-dependent estimates, exact parameter budgets, logarithmic energy
arguments, summable reconstruction, and new extensions are proved here.
The fixed-parameter theorem in the neighboring project does not prove the
scale-dependent gauge theorem.

The development is AI-assisted through Codex, as recorded in
`formalization.yaml`. No independent human review or endorsement by the
listed projects is asserted.
