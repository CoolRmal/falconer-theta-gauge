# Theorem 1.1: formal statement and initial verified lemmas

October 8, 2026. This notebook records an incomplete formalization. The main
theorem remains a proof obligation and is not comparator certified.

## Exact target

The uploaded manuscript defines

$$
h_\theta(r)=r\exp\!\left(-\bigl(\log(1/r)\bigr)^\theta\right),
\qquad 0<r<1,\qquad h_\theta(0)=0.
$$

For a compact subset of the Euclidean plane, its Theorem 1.1 states

$$
\frac23<\theta<1,\qquad \mathcal H^{h_\theta}(E)>0
\quad\Longrightarrow\quad
\mathcal L^1(\Delta(E))>0,
\qquad \Delta(E)=\{\lVert x-y\rVert:x,y\in E\}.
$$

The Lean definitions use the Euclidean norm and Mathlib's general Hausdorff
measure constructor. The gauge is extended by the identity for radii at least
one, which does not affect the limit over covers with diameters tending to zero.
The exact covering characterization has been proved:

$$
\mathcal H^{h_\theta}(E)=
\sup_{\rho>0}\ \inf_{\substack{E\subseteq\bigcup_{n=0}^{\infty} U_n\\
\operatorname{diam}(U_n)\le\rho}}
\sum_{\substack{n\ge0\\U_n\ne\varnothing}}
h_\theta\bigl(\operatorname{diam}(U_n)\bigr).
$$

The independent Challenge imports only Mathlib and repeats the transparent
custom definitions. The Solution imports the development without importing
Challenge. The target includes no auxiliary energy or projection hypothesis.

## Verified geometric foundation

For positive radii below one, the gauge is positive and at most the radius:

$$
0<h_\theta(r)\le r\qquad(0<r<1).
$$

Indeed, the exponential is positive, and its exponent is nonpositive because
the logarithm and its real power are nonnegative. At zero the gauge is zero.
Gauge comparison then gives

$$
\mathcal H^{h_\theta}(E)\le\mathcal H^1(E).
$$

In particular singletons and countable sets have zero gauge measure. Positive
gauge measure supplies two distinct points of the set, so the distance set
contains a strictly positive number. This alone does not prove positive length.

The map from the product of the set with itself to its distance set is
continuous. Consequently a compact set has a compact, Lebesgue-measurable
distance set. This establishes that the target's use of Lebesgue measure has
the intended measurable-set interpretation.

## Verified scalar summability

For every positive exponent and every positive coefficient, Mathlib's
logarithmic asymptotic estimate gives the following eventual bound, now proved
in the project:

$$
\log n\le c n^s\qquad(n\text{ sufficiently large}),\qquad s,c>0.
$$

Taking the coefficient to be half the exponential-decay coefficient yields

$$
\log n\le\frac c2 n^\theta
\quad\Longrightarrow\quad
e^{-c n^\theta}\le e^{-2\log n}=n^{-2}.
$$

Comparison with the inverse-square series proves

$$
\sum_{n=0}^{\infty} e^{-c n^\theta}<\infty
\qquad(\theta>0,\ c>0).
$$

The parameter threshold used to absorb branch-counting costs is also exact:

$$
3\theta-2>0\quad\Longleftrightarrow\quad\theta>\frac23.
$$

Thus the logarithm is eventually dominated by an arbitrarily small positive
multiple of the power with exponent three theta minus two. The modeled filter
error power is summable because

$$
\theta>\frac23
\quad\Longrightarrow\quad
-8(2\theta-1)<-1,
\qquad
\sum_{n=0}^{\infty}n^{-8(2\theta-1)}<\infty.
$$

These are scalar results. The geometric estimates that supply the corresponding
shell energies and filter errors remain to be proved.

## Remaining proof obligations

The manuscript's proof requires a gauge Frostman measure, endpoint Orlicz
radial projection bounds, summable Fourier reconstruction, regular decomposition
with explicit parameter dependence, four uniform energy estimates, and the
multiscale budget induction. Fixed-parameter theorems cannot be used at
scale-dependent parameters without proving the needed uniform dependence.

The main target has one explicit proof hole. Comparator permits only
`propext`, `Quot.sound`, and `Classical.choice`, so it must reject the current
target's dependence on `sorryAx`. Registration on Palomar requires the completed
proof, successful verification of the exact public commit, truthful metadata,
and the registry review. None of those later statuses is asserted here.
