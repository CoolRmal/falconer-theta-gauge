# Theorem 1.1: formal statement and verified foundations

October 9, 2026. This notebook records an incomplete formalization. The main
theorem remains a proof obligation and is not comparator certified.
Author and responsible maintainer: Yongxi Lin.

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

The full parameter Lemma 2.2 is now proved, including all four groups of
budgets above one common threshold, for the actual rounded quantities. The
coarse bound on the expansion count is `T+1 ≤ 242N`; logarithmic domination
absorbs its polynomial constants. The inverse tolerance is controlled by the
inverse square block parameter, so the regular-part and branch counts are
absorbed by the growth of the cubic block parameter times the scale.
All three terms in the asserted filter bound are summable at the actual
parameters: the inverse eighth power of the scale-multiplied tolerance, the
scale times its dyadic exponential, and the dyadic block exponential.
The geometric removed-mass estimate itself remains to be proved.

## Verified gauge Frostman measure and logarithmic energies

For the stronger range of exponents below, the full gauge Frostman construction
is proved:

$$
0<\theta\le1,\quad E\text{ compact},\quad\mathcal H^{h_\theta}(E)>0
\quad\Longrightarrow\quad
\exists\mu,C>0:\ \mu(E)=1,\ \operatorname{supp}\mu\subseteq E,
\quad \mu(\overline B(x,r))\le C h_\theta(r)\quad(0<r<1).
$$

The proof first converts positive Hausdorff gauge measure to positive gauge
content. Finite dyadic trees supply nonnegative weights with positive total
mass and saturated covering bounds. After normalization, the atomic probability
measures lie on the compact set. Compactness in the weak topology provides a
subsequence and a probability limit. Portmanteau transfers the open-ball bounds;
dyadic radius comparison and gauge doubling yield all the closed-ball bounds.

This measure has no atoms. For every fixed logarithmic exponent, it has finite
critical logarithmic energy:

$$
J_\gamma(\mu)=\iint
\frac{(1+\log^+(1/\lVert x-y\rVert))^\gamma}{\lVert x-y\rVert}
\,d\mu(x)\,d\mu(y)<\infty,\qquad \gamma\ge1.
$$

The formal kernel is infinite on the diagonal. Its finiteness is proved by
dyadic annuli, with each annular potential bounded by a constant times

$$
(n+1)^\gamma\exp(-c n^\theta).
$$

Polynomial factors are absorbed by half of the stretched exponential, giving
a summable majorant. This establishes the genuine energy, including the
diagonal, rather than a totalized real quotient which would vanish at zero.

The actual dyadic Gaussian kernel also satisfies

$$
K_\gamma(r)=\sum_{n\ge0}(n+1)^\gamma 2^n e^{-4^n r^2}
\le C_\gamma\frac{(1+\log(1/r))^\gamma}{r},\qquad0<r<1,\quad\gamma\ge0.
$$

Splitting at the dyadic scale nearest the inverse radius controls the finite
prefix and compares the shifted tail with the convergent kernel at radius one.
Gaussian Fourier duality and Tonelli now connect this scalar kernel to actual
planar probability measures, proving the full Lemma 5.2:

$$
\int_{\mathbb R^2}|\widehat\mu(\xi)|^2
\frac{\log^\gamma(e+\lVert\xi\rVert)}{\lVert\xi\rVert}\,d\xi
\le C_\gamma(1+J_\gamma(\mu)),\qquad\gamma\ge0.
$$

The Fourier phase is exactly that of the manuscript. The inverse norm at the
origin is extended nonnegative; its integral over a bounded planar ball is
proved finite. No finiteness assumption is hidden in the weight definition.

Two compact pieces of positive mass are also extracted and normalized.
A positive similarity puts them in discs of radius `1/400` inside the unit
square, with centers exactly `1/4` apart and pair distances between `0.24`
and `0.26`. Their probabilities retain the gauge bounds and all logarithmic
energies. Positive distance-set length transfers back under this similarity.

## Verified reconstruction bridges

Dyadic frequency shells overlap at most three times. The resulting quadratic
L² bound proves convergence of square-summable shell pieces. The actual smooth
low-pass kernels preserve mass; their differences have uniformly bounded L¹
norm and the precise dyadic Fourier support. Convolving a removed measure with
these differences gives an L¹ error bounded by a constant times its removed
mass. Low-pass convolutions converge to the original measure on Schwartz tests.

The final absolute-continuity implication is also proved. If a finite positive
measure satisfies, for an integrable function and an L² function,

$$
\int\varphi\,d\alpha
=\int\varphi f\,dx+\int(\mathcal F^{-1}\varphi)g\,d\xi,
\qquad f\in L^1,\quad g\in L^2,
$$

then Cauchy–Schwarz and Plancherel bound this pairing by

$$
\int|\varphi|\,d\sigma+\lVert g\rVert_2\lVert\varphi\rVert_2,
\qquad d\sigma=|f|\,dx.
$$

Smooth cutoffs on compact subsets of an open set yield

$$
\alpha(U)\le\sigma(U)+\lVert g\rVert_2|U|^{1/2}.
$$

Outer regularity provides open covers with both terms tending to zero for any
Lebesgue-null set. Hence the measure is absolutely continuous. The actual
L² shell pieces and the telescoped series pairing are constructed,
completing the manuscript's Lemma 4.2. For any finite positive measure and
eventually dominated approximants, the exact criterion is

$$
\sum_{N\ge N_0}\bigl(\alpha(\mathbb R)-\tau_N(\mathbb R)\bigr)<\infty,
\qquad
\sum_{N\ge N_0}\int_{2^{N-1}\le|r|\le2^{N+1}}
|\widehat\tau_N(r)|^2\,dr<\infty
\quad\Longrightarrow\quad\alpha\ll\mathcal L^1.
$$

The actual product-distance probability has mass one on the all-pairs distance
set. Its absolute continuity therefore implies positive Lebesgue length.

## Verified projection foundations

The orthogonal-projection development constructs a jointly Borel nonnegative
density for almost every direction whenever the weighted Fourier energy is
finite. Its fibers are the actual projection densities and satisfy the exact
one-dimensional Plancherel identity. A smooth low-pass decomposition bounds
the squared-density mass above an amplitude threshold by the corresponding
high-frequency Fourier tail. Summing the logarithmic amplitude layers proves
the literal one-dimensional estimate

$$
\int_{\mathbb R} f(t)^2\log^\gamma(e+f(t))\,dt
\le C_\gamma\int_{\mathbb R}|\widehat\nu(r)|^2
\log^\gamma(e+|r|)\,dr,\qquad\gamma\ge1,
$$

for the actual density of a probability with square-integrable Fourier
transform. These estimates have no extra logarithmic exponent. Polar Fourier
integration now gives the full averaged Lemma 5.3:

$$
\int_{S^1}\int_{\mathbb R} F(w,t)^2\log^\gamma(e+F(w,t))\,dt\,dw
\le C_\gamma E_\gamma(\mu).
$$

The jointly Borel density is the actual orthogonal projection density for
almost every direction.

For radial projections, the inverse-distance-weighted smooth source has an
exact ray-density identity with respect to circle arc length. The polar
Jacobian cancels the inverse-distance factor. Extending rays to whole lines
and applying the orthogonal density estimate gives the smooth transfer.
Uniform logarithmic bounds also imply the actual cutoff estimate

$$
\sigma_n(A)\le H\lambda(A)+\frac{K}{\log^p(e+H)},\qquad p>0.
$$

Portmanteau transfers this estimate to a weak probability limit. Outer
regularity extends it from open sets to arbitrary sets. Letting the cutoff
grow proves absolute continuity of the limit. A uniform moment of order two
greater than the desired exponent also gives finite lower Orlicz moments for
the limit's actual Radon–Nikodym density. The target-specific radial endpoint
and uniform spread preparation are now assembled below.

## Verified regular decomposition

Lemma 5.8 is proved for the original measure weights. The actual half-open
unit square has exactly the required terminal-cell count. The construction
discards light terminal cells, assigns bottom-up types using original masses,
and discards whole light type fibers. The floor and ceiling schedule is exact:

$$
\Delta=\lfloor\varepsilon N/4\rfloor,\qquad
w=\lfloor\varepsilon N/8\rfloor,\qquad
k=\lceil N/\Delta\rceil.
$$

Actual parent-child counts bound each class drop, yielding at most ten choices
per sampled level. The type count and (P2) give

$$
\#\{\text{types}\}\le(48/\varepsilon+1)10^{8/\varepsilon+1}
\le2^{\kappa N/4}.
$$

Each retained Borel carrier is a union of original positive-mass terminal
cells. The carriers are disjoint and have the exact bounds

$$
\mu(G_t)\ge2^{-\kappa N/2},\qquad
\mu\left([0,1)^2\setminus\bigcup_tG_t\right)\le2\,2^{-\kappa N/4}.
$$

Restricting to a carrier preserves each retained terminal-cell weight.
Every coarser restricted cell mass equals the corresponding original-weight
fiber sum. The sampled-level comparisons interpolate to every depth through
the terminal scale, and normalization multiplies all masses by one factor:

$$
\rho_t(Q)\le2^{\varepsilon N}\rho_t(P)
\quad(0\le n\le N,\ P,Q\text{ depth-}n\text{ cells},\ \rho_t(P)>0),
\qquad\rho_t=\frac{\mu|_{G_t}}{\mu(G_t)}.
$$

This is the manuscript's regularity condition under its finite-depth
convention. All carriers, measures, counts, and mass estimates are concrete.

## Verified maximal-cell excess bounds

The maximal cell mass is an actual attained maximum over the finite cells of
the unit square. For every probability carried there, its successive values
satisfy

$$
M(0)=1,\qquad M(n+1)\le M(n)\le4M(n+1),\qquad M(n)>0.
$$

The source's excess function is defined from these actual masses by

$$
M(n)=2^{-n}2^{-NA(n)}.
$$

The successor bounds give its exact Lipschitz constant. The retained-part mass
threshold and the original gauge bound give the lower excess estimate. Each
cell fits in a ball of radius exactly its side length about its midpoint, so
no extra radius factor enters this argument. Under the manuscript's constant
budget, all four conclusions of Lemma 5.10 are proved:

$$
A(0)=0,\qquad |A(n)-A(m)|\le\frac{|n-m|}{N},\qquad
g(n)-\kappa\le A(n)\le\frac nN.
$$

The bounds concern the actual normalized restriction, with no independently
postulated excess function.

## Verified radial endpoint and uniform spread

The gauge supplies every logarithmic energy order. Smooth compact probability
approximations contract their Fourier energies and stay in a common carrier
separated from the pins. The averaged orthogonal estimate and the exact
smooth polar identity bound the actual joint radial densities at a stronger
Orlicz order. Their joint measures converge weakly; the proved Orlicz limit
argument identifies the actual Radon–Nikodym density of the limit. Thus the
prepared radial projections are absolutely continuous and have finite moments
at every desired order for almost every pin. This target-specific argument
uses stronger energies than the general single-order Theorem 5.4.

Write the eighth-order radial moment as

$$
Q(x)=\int_{S^1}\Phi_8(F_x(w))\,dw,
\qquad \Phi_8(t)=t\log^8(e+t).
$$

Joint measurability makes the good-pin sets with bounded moment Borel. Since
these sets exhaust a full-measure set, one has mass greater than one half.
Inner regularity gives a compact subset with original mass greater than one
quarter. Restrict and normalize both sources to these compact sets. Each
restricted radial measure is at most four times its original radial measure;
the actual RN densities satisfy the same domination almost everywhere.
The elementary scaling estimate is proved:

$$
\Phi_8(4t)\le4(1+\log4)^8\Phi_8(t),\qquad t\ge0.
$$

A common finite bound therefore holds at **every** retained pin in both
directions. The new probabilities retain the small separated discs, actual
compact carriers, and all logarithmic energies. Their common gauge constant
increases by at most four. This proves the uniform spread requirement of
Proposition 5.6(c), with the actual radial densities.

The logarithmic small-set estimate is also proved for actual densities:

$$
\int_ZF\le H|Z|+K(\log H)^{-8},\qquad H>1.
$$

For the manuscript's bad-direction length budget, choosing its inverse square
root gives the exact bound by a dyadic exponential plus an inverse eighth
power. The finite-test weighted loss is now proved below; the full construction
still needs the assembly of each regular piece's own test list.

## Verified entry depth and finite test schedule

Actual regular-part cell masses now give the source's occupied-descendant
count, rather than a postulated counting bound. The entry depth is the last
integer depth at which the actual excess is at most the gain:

$$
c=\max\{n\le N:A(n)\le\beta\}.
$$

The exact parameter facts and gauge lower barrier prove all the entry bounds
of Lemma 9.2, including the post-entry budget:

$$
\lfloor\beta N\rfloor\le c<N/4,\qquad 100q<N-c,
\qquad A(n)>\beta-1/N\quad(c\le n\le N),
$$

$$
V([c,N])\ge2\beta-2/N,\qquad k_c[0,c]\le\beta+\kappa.
$$

The finite interval minima define the actual trimmed budget. Its inclusion
monotonicity and split gains are proved from actual minimum plateaux. The
constructed split uses marked block minimizers and gives the length margins
that pay the positive costs of the three moves.

Contributing tube and projection tests are concrete finite records with
anchors, endpoints and lengths. Their scheduled lists run over the actual
long subintervals, are monotone under interval inclusion, and retain each
contributing origin. Anchor depths lie in the constructed marks and every
length is at most half its origin's length. The mark count and the exact
parameter budget give at most **N²** tests per list, proving Lemma 8.3(b,c).
The actual chains and finite trees are now constructed below. Their analytic
energy recurrences remain to be proved.

## Verified uniform nonstationary estimates and smooth bumps

For a smooth amplitude with derivative bounds

$$
\|a^{(j)}\|_\infty\le A M^j\quad(j\le K),\qquad M\ge1,
$$

assume the actual phase derivative has norm at least a positive number
on an open neighborhood of the amplitude's closed support, and its higher
derivatives through order k+1 have norm at most a common constant. A globally
smooth regularized reciprocal agrees with the true inverse there. Exact
Leibniz coefficients and factorial bounds give the source's polynomial base:

$$
\left|\int e^{i\phi}a\right|
\le |\operatorname{supp}a|\,A
\left(\frac{2(k+1)^2\max\{M,\Lambda/\lambda\}}{\lambda}\right)^k.
$$

The smooth compact real-line form and the smooth periodic form are both
proved. For the latter, endpoint terms cancel over an actual period, and its
length replaces the support length. For a linear phase, the transported
amplitude is exactly the kth derivative times the kth power of the constant
inverse slope; the sharper base M divided by the slope lower bound allows
M below one. No unspecified order-dependent derivative constants are used.

For every finite order K there is a genuine smooth, nonnegative, even
probability bump with compact support in $[-1,1]$ and

$$
\int_{\mathbb R}|\omega_K^{(k)}(x)|\,dx
\le(\pi^2/6)^k(k!)^2,\qquad 0\le k\le K.
$$

Its construction convolves normalized boxes of half-widths $6/(\pi^2 j^2)$,
with a smooth probability tail inside the remaining
support radius. The fundamental theorem of calculus differentiates each box
average into its boundary difference. The L¹ cost is exactly the inverse box
width, giving the factorial product. The Basel identity makes the remaining
radius positive. This finite-order construction suffices for the later
finite-order masks; an infinite-product identity is not claimed.

## Verified directional masks and weighted filter loss

The tube count uses actual occupied dyadic cell centers in the literal
Euclidean tube. The projection count uses actual pair coincidence under
the normalized anchor-cell restriction. Both are measurable and antipodally
symmetric. Markov's inequality gives the exact failure length

$$
|\mathrm{Bad}_{\mathrm{test}}|\le2\pi\,2^{-2\varepsilon N}.
$$

Convolving the indicator of a closed neighborhood of an arbitrary passing
set with the finite-order bump gives an actual smooth mask between zero and
one, equal to one on the passing set. Periodic descent gives a function on
the circle. A finite partition into occupied anchor cells proves joint
measurability in the pin and direction. Its angular derivative bounds are

$$
\|b^{(k)}\|_\infty\le\left(\frac{(4T)^3}{\sigma}\right)^k,
\quad k\le6T,\qquad \sigma=\min\{1,2^{-\ell}R^\varepsilon\}.
$$

The weighted distance source and its masked versions are literal measures:

$$
\alpha=\operatorname{dist}_\#\bigl(|x-y|^{-1/2}(\mu_1\times\mu_2)\bigr),
\qquad
\tau_N=\operatorname{dist}_\#\bigl(M_N(x,y)|x-y|^{-1/2}
(\mu_1\times\mu_2)\bigr).
$$

On the prepared carriers, the weight lies between one and 2.1. Finite lists
of at most N²+1 genuine tests give a Borel pair mask. The proved regular
decomposition supplies the actual carrier defects. The Orlicz estimate then
proves domination and the exact summable removed-mass bound:

$$
\tau_N\le\alpha,\qquad (\alpha-\tau_N)(\mathbb R)\le a_N,
$$

$$
a_N=2.1\left(4R^{-\kappa/4}
+2\left[3(N+1)R^{-\varepsilon}+2^8K(\varepsilon N)^{-8}\right]\right),
\qquad \sum_N a_N<\infty.
$$

The concrete constructor now assembles the individual lists of every retained
regular piece into one Borel filter. Neutral padding uses exactly N²+1 shared
slots. Its carrier is the literal regular carrier, so the displayed removed-mass
bound applies to the actual scheduled filtered distance measure.

## Verified actual chains, trees, and scalar binning

The six actual move types have explicit child states. Every move strictly
decreases the interval width, so unfolding terminates. Nodes are genuine
chains with proved transitions. A multiset version preserves multiplicities
when several paths reach the same state. Exact parameter budgets prove

$$
\#\mathrm{ordinary\ moves}\le7/\kappa,\qquad
\#\mathrm{all\ moves}\le7/\kappa+1/\varepsilon,\qquad
\#\mathrm{tree\ visits}\le R^\kappa.
$$

The actual chain costs telescope against the constructed interval minima.
For every depth n in its final interval, including short final intervals,

$$
\sum\mathrm{cost}\le2A(n)+22\kappa-V(\mathrm{root}),\qquad
\prod\mathrm{multiplier}\le R^{\sum\mathrm{cost}+2\kappa}.
$$

Mask levels remain below the source's finite derivative-order bounds. The
literal entry-piece list has at most N²+1 tests, includes the entry tube, and
drops precisely that tube when restricted above the entry depth. The
numerical energy-closing and final-shell inequalities are proved from the
exact parameter facts. Analytic recurrences for the four actual energies
are still required before the tree can prove their estimates.

For a finite positive measure on the line, write

$$
C_\eta(h,u)=(\eta\times\eta)\{|s-t-u|\le h\},\qquad h>0.
$$

Actual half-open bins form a disjoint measurable partition. Discrete
Cauchy--Schwarz gives the manuscript's first three binning estimates:

$$
C_\eta(h,u)\le4C_\eta(h,0),\qquad
C_\eta(Lh,0)\le(2L+1)C_\eta(h,0)\quad(L\in\mathbb N),
$$

$$
\iint(1+|s-t|/h)^{-2}\,d\eta(s)d\zeta(t)
\le10\sqrt{C_\eta(h,0)C_\zeta(h,0)}.
$$

The decaying-kernel argument uses an actual summable integer-shift majorant.
Both Fourier comparisons are now proved as well, as described below.

## Verified quadratic phase and circular Morse substitution

The quadratic Fourier identity is proved by a genuine complex Gaussian,
followed by dominated convergence as the positive damping tends to zero.
The complex square-root branch is evaluated exactly. The purely imaginary
Taylor remainder has the sharp factorial bound, with no exponential loss.
Every required Fourier moment is an actual integrable Schwartz derivative.
Two adjacent derivative norms give an integrable Cauchy majorant of total
mass one half in Mathlib's normalized frequency variable.

For Schwartz amplitudes, and therefore for smooth compact amplitudes, the
source's exact expansion and error are proved in both signs:

$$
\int e^{i\Lambda s^2/2}g(s)\,ds
=\sqrt{2\pi/\Lambda}\,e^{i\pi/4}
\sum_{j<T}\frac{(i/(2\Lambda))^j}{j!}g^{(2j)}(0)+E,
$$

$$
|E|\le\sqrt{2/\Lambda}\,\frac{(2\Lambda)^{-T}}{T!}
\bigl(\|g^{(2T)}\|_1+\|g^{(2T+2)}\|_1\bigr),\qquad \Lambda>0.
$$

This checkpoint claims the smooth-amplitude version used by the constructed
masks; the manuscript's full finite-regularity version is not claimed.
The literal circular coordinate and its Jacobian satisfy

$$
\vartheta(s)=2\arcsin(s/2),\qquad
\vartheta'(s)=(1-s^2/4)^{-1/2},\qquad
\cos\vartheta(s)=1-s^2/2.
$$

If a smooth cutoff vanishes outside the angular interval of radius π/3,
the actual transformed product with the Jacobian is smooth and supported
in [-1,1]. An ordinary integral substitution identifies the localized
cosine integral with its quadratic integral. Its finite expansion follows
with the actual derivatives of this compact amplitude. Universal real
coefficients are defined by finite Leibniz and Faà di Bruno sums of the
literal coordinate derivatives. The positive and conjugate operators have
proved exact scaled derivative identities, constant term one, and degree at
most 2j. Actual weighted coefficient norms and uniform localized amplitude
derivative bounds are now proved, as described below.

## Concrete directional averages and assembled filters

The prepared carrier directions lie in one compact closed arc of angular
length at most 1/20. The proof controls the actual relative complex
displacement, so it also handles arcs crossing the principal-angle branch.

Nine actual half-open dyadic cells cover each closed disc of dyadic radius,
including boundary points. The regular measure's cell bounds therefore apply
to the literal normalized anchor probabilities. Circle sine and cosine band
estimates, Tonelli, and finite dyadic shells prove the exact Lemma 6.5 bounds:

$$
\bar N_P\le R^{\operatorname{ht}[g,p]+4\varepsilon},\qquad
\bar\Pi_P\le 2^{-(u-p)}R^{\operatorname{ht}[p,u]+4\varepsilon}.
$$

The parameter facts absorb the actual intermediate factors 150(N+4) and
75(N+2). Passing directions gain the additional factor R^{2ε}. Literal
angular widening is proved even at closed-neighborhood boundaries; it does
not require the passing set itself to be closed. Each mask derivative
vanishes where the next narrower level fails.

The disjoint regular-piece carriers provide a finite Borel pin partition.
Each piece contributes its own actual scheduled tests. Neutral padding
preserves their product, and the assembled symbol is smooth in the angular
variable at every pin. Its derivative scale is bounded by

$$
(N^2+1)(4T)^3\max(1,2^{L-\varepsilon N}),
$$

where L is the true maximum length in that piece's finite test list. This
supplies the concrete filter data for the proved removed-mass estimate.

## Fourier binning and the actual masked Fourier energy

For the literal angular Fourier transform of a finite positive measure, an
actual two-box identity gives the remaining two binning inequalities:

$$
C_\eta(h,0)\le2h\int_{|r|\le h^{-1}}|\widehat\eta(r)|^2\,dr,
\qquad
\int_{|r|\le h^{-1}}|\widehat\eta(r)|^2\,dr
\le160h^{-1}C_\eta(h,0).
$$

This completes all four parts of Lemma 7.3 without a Fourier identity assumed
as a hypothesis. The diagonal remains in the actual collision measure.

The Fourier energy now consists of literal integrals, with the manuscript's
actual smooth frequency cutoff Ψ. Its derivative bound is 14^k(k!)² at the
chosen finite order; its support and plateau give the required dyadic window.
For bounded measurable masks the actual U, σ and F satisfy

$$
F_{X,Y}(v)\le2600\,4^v\rho_1(X)\rho_2(Y),
\qquad
F_{X,Y}(v)\le2600\,4^{v-a}R^{-2A(a)}
$$

in the one-piece cell case. A reached mask is a direction-only factor on an
actual descendant cell, so removing it can only increase this actual energy.
These are the starting bounds; the four nontrivial energy estimates remain.

## Uniform localized derivatives and exact inverse operators

The genuine holomorphic Jacobian on complex discs of radius one half obeys
Cauchy's estimates. Restriction to the real axis commutes with every
iterated derivative, giving, uniformly on |s|≤1,

$$
|J^{(n)}(s)|\le2\,n!\,2^n,\qquad
|\vartheta^{(m)}(s)|\le2^m(m-1)!\quad(m\ge1).
$$

The cutoff χ₀ is the actual interval indicator convolved with the finite-order
bump of radius π/12. It equals one on the interval of radius π/6, is supported
in the interval of radius π/3, and obeys |χ₀^{(k)}|≤(2π)^k(k!)² through the
selected order. Finite Faà di Bruno partitions give the actual localized
amplitude g the uniform bounds

$$
|g^{(n)}(s)|\le2A(n!)^2(56M)^n,
\qquad \|g^{(n)}\|_1\le4A(n!)^2(56M)^n.
$$

The localized expansion therefore has an explicit uniform remainder in
universal operator form. The literal coefficient sums satisfy

$$
\|P_j\|_M\le(100jM^2)^j\quad(j\ge1).
$$

The proof counts actual cyclic partition weights, whose sum is exactly n!.
It does not assume the source's individual coefficient estimate. Literal
polynomials define the inverse recursion and prove

$$
Q_0=1,\qquad Q_j=-\sum_{i=1}^jP_iQ_{j-i},\qquad
\deg Q_j\le2j,\qquad \sum_{i=0}^jP_iQ_{j-i}=0\quad(j\ge1).
$$

Their polynomial multiplication is proved to agree with differential
composition on smooth amplitudes, including the conjugate operators.
The numerical inverse norms and the full periodic expansion for smooth amplitudes
are now proved, as described below.

## Numerical inverse norms and finite inversion

The weighted norm is the actual finite sum of coefficient magnitudes. Its
triangle and multiplication inequalities follow from polynomial coefficient
expansion. The literal recursion proves the stronger uniform estimate

$$
\|Q_j\|_M\le(200NM^2)^j\quad(j\le N),\qquad
\|Q_j\|_M\le(800jM^2)^j.
$$

Applying a polynomial of degree at most d to an actual amplitude consumes d
input derivatives and multiplies its amplitude bound by its weighted norm.
This is proved at finite differentiability order, also for conjugate operators.

Let C_m be the degree-m coefficient of the two series truncated at T. Actual
polynomial convolution gives

$$
C_0=1,\quad C_m=0\ (0<m<T),\qquad
\|C_m\|_M\le(m+1)(800mM^2)^m.
$$

The finite product of the actual differential series equals the input
amplitude plus precisely the terms of total order at least T. For a smooth
(A,M)-regular amplitude through order 4T and 0≤q≤1/2, its tail satisfies

$$
\|\mathrm{Tail}\|\le2A(2T+1)q^T,
\qquad 800(2T)M^2|z|\le q.
$$

No cancellation or tail estimate is supplied as an analytic hypothesis.

## Full periodic circular expansion for smooth amplitudes

The actual periodized cutoff is locally a single translate. Near and opposite
cutoffs have disjoint supports. Their complement is smooth, periodic and
supported where the sine of the phase angle has magnitude at least 1/2.
The exact circle integral splits into two localized Morse integrals and this
actual away integral.

For a smooth periodic amplitude G that is (A,M)-regular through order 2T+2,
M≥1 and Λ≥1, the proved expansion is

$$
\int_u^{u+2\pi}e^{-i\Lambda\cos(t-\varphi)}G(t)\,dt
=\sqrt{2\pi/\Lambda}\left[
 e^{-i(\Lambda-\pi/4)}\sum_{j<T}\Lambda^{-j}P_jG(\varphi)
 +e^{i(\Lambda-\pi/4)}\sum_{j<T}\Lambda^{-j}\bar P_jG(\varphi+\pi)\right]+E,
$$

$$
|E|\le A\sqrt{2\pi/\Lambda}\,B(B/\Lambda)^T,
\qquad B=10^8(T+1)^4M^2.
$$

The proof uses T+1 integrations by parts for the away contribution. This
retains the square-root normalization and fits the available derivative
budget. The manuscript's finite-regularity version is not claimed here;
the actual constructed masks are smooth at every order.

The prepared direction arc has a literal convolution cutoff ψΓ. It equals
one on Γ enlarged by 0.1, vanishes outside Γ enlarged by 0.2, and vanishes
throughout the opposite arc's neighborhood of radius π/3. Its actual angular
derivatives obey 33^k(k!)² through the selected finite order.

## Actual weighted distance energy and the Fourier bridge

The passing distance measure is the pushforward of the actual restricted
product weighted by inverse square-root distance and the passing indicator.
Positive separation proves that it is finite. Its normalized collision energy
D satisfies both exact trivial bounds (7.2); literal passing sets give
monotonicity under level increase, list removal and width enlargement.
The actual Fourier transform equals the weighted spatial double integral by
measure pushforward and Fubini.

For finite positive measures η≤β≤ζ, normalization m≥0 and 0≤s≤t, the genuine
low/high bridge is proved:

$$
D_\eta(t)\le320D_\zeta(s)
 +\frac{320}{m}\sum_{s<v\le t}
 \int_{2^{v-1}\le|r|\le2^v}|\widehat\beta(r)|^2\,dr.
$$

The proof allows real s and includes a partial first dyadic shell. Its
stronger high-frequency coefficient is two; the displayed source constant
320 follows. For the actual ordered scheduled lists, the literal masks give
passing ≤ masked ≤ next-level passing measures. This instantiates the bridge
at s=t−εN and proves Lemma 7.4 with its source constant. The four nontrivial
energy estimates are the next analytic assembly.

## Concrete scheduled symbols and spatial separation

The symbol class is the actual finite product of normalized angular mask
derivatives, multiplied by a Borel spatial weight bounded by one. Its order
is the sum of the derivative orders. Measurability, the bound by one, and the
next-level passing implication follow from these actual factors.

To differentiate symbols of initial order at most 2T up to another 6T times,
the construction chooses the finite bump order K=8T. The existing 6T bounds
remain valid. Each true derivative has a finite Leibniz expansion into symbols
of the increased order, with total coefficient magnitude at most

$$
M_L^j,\qquad M_L=128T^2|L|\max(1,2^{\max\operatorname{length}(L)-\varepsilon N}).
$$

Dropping reached factors contracts the actual Fourier energy. The state
energies in Definition 8.4 are genuine suprema and finite cell maxima of these
actual energies; their trivial bounds follow from the actual cell masses.

For balls of radius ρ with centers x₀,y₀ separated by D≥50ρ, the genuine
inverse-distance power has a uniformly convergent separated polynomial series

$$
|x-y|^{-j}=\sum_{n=0}^{\infty}\gamma_n p_n(x)q_n(y),\qquad
|p_n(x)|,|q_n(y)|\le1,\qquad
\sum_n|\gamma_n|\le(\sqrt2/D)^j.
$$

Absolute convergence and uniform convergence on the product of the closed
balls are proved. This is stronger than the coefficient constant in Lemma 3.9.

The short terminal-state bounds are also actual energy estimates. For a true
move chain whose final interval has length at most 100κN, its actual multiplier
product pays the final energy at every mask level:

$$
\mathrm{Mult}(\mathrm{chain})\,
\mathcal E_\rho(\mathrm{final})
\le2^{N(-V(\mathrm{root})+225\kappa)}.
$$

This follows from the actual excess bounds and the proved chain cost; no
terminal-energy bound is assumed.

## One-sided inversion for the actual masks

The prepared cutoff equals one near the true pair directions and vanishes
near their opposite directions. Thus the opposite stationary series vanishes
term by term. The finite P/Q convolution leaves exactly the high-order tail.
The correct complex normalization is

$$
c_1=(\sqrt{2\pi})^{-1}e^{-i\pi/4}.
$$

For the actual pair of scheduled symbols, the proved pointwise inversion is

$$
\left|d^{-1/2}e^{-ird}B(\varphi)-c_1\sqrt r
\sum_{j<T}(rd)^{-j}\int_u^{u+2\pi}e^{-ird\cos(t-\varphi)}
\psi_\Gamma(t)Q_jB(t)\,dt\right|\le2^{-200N}.
$$

Here d>0, r>0, the true direction lies in Γ, and the source frequency,
list-length, cardinality and terminal-distance conditions hold. The actual
symbol derivative scale satisfies the needed frequency and terminal budgets,
including an empty list. ParameterFacts proves the geometric ratio bound

$$
\varpi\le2^{-7\varepsilon N/8},\qquad
\varpi^T\le2^{-210N}.
$$

The proof retains the square-root normalization in the stationary remainder.
No pointwise inversion result is supplied as a hypothesis.

## Actual bilinear Cauchy–Schwarz and countable expansions

For the actual Fourier amplitudes U_X,U_Y, a measurable circle weight bounded
by one, and r>0, define the literal integral

$$
Z(r)=\sqrt r\int\psi(w)U_X(r,w)\overline{U_Y(r,w)}\,dw.
$$

The actual circular Cauchy–Schwarz inequality, including zero cell masses, gives

$$
|Z(r)|^2\le\rho(X)\rho(Y)\,\sigma_X(r)\sigma_Y(r)/r.
$$

The genuine smooth frequency window equals one on [2ᵛ/2,2·2ᵛ]. Integration
of this inequality on that interval is bounded by 2ρ(X)ρ(Y)F_X,Y(v).
For actual measurable coefficients |cₙ(r)|≤aₙ with nonnegative summable aₙ,
the countable extension proves convergence and the integrated estimate

$$
\int_{2^{v-1}}^{2^{v+1}}\left|\sum_n c_n(r)Z_n(r)\right|^2dr
\le2\rho(X)\rho(Y)\left(\sum_n a_n\right)
\left(\sum_n a_nF_n(v)\right).
$$

Dominated convergence justifies the genuine countable series and integral
interchange. These are completed analytic tools for Step 3 of Estimate 7.5;
the full spatial and operator assembly is recorded below.

## Equal arcs, genuine links, and Schur's bound

For 0<ℓ≤1, M=⌈2π/ℓ⌉ equal periodic cells have actual width w=2π/M satisfying
ℓ/2≤w≤ℓ and M≤8/ℓ. The literal source cutoffs are

$$
\chi_k=1_{A_k}*\omega_{w/4},\qquad \sum_k\chi_k=1,\qquad
|\chi_k^{(j)}|\le(576T^2/\ell)^j\quad(j\le6T).
$$

Their actual support lies within chord distance ℓ of the arc center. The
quarter turn is the genuine planar right-angle isometry. True dyadic cell
centers and actual points satisfy the necessary phase replacement bounds.
For the manuscript's ℓ=min(1,2⁻ᵖ/2⁻ᵃ·2ᴱ), τ=2⁻ᵖ·2³ᴱᐟ² and 2ᴱᐟ²≥12,
an unlinked pair of cell pairs has either a radial phase or one of the two
angular phase derivatives of magnitude greater than τ/2.

For any actual finite symmetric linking graph with row degree at most D,
Schur's argument proves

$$
\left\|\sum_\alpha z_\alpha\right\|^2\le
D\sum_\alpha\|z_\alpha\|^2+
\sum_{\alpha\not\sim\beta}|\langle z_\alpha,z_\beta\rangle|.
$$

All unlinked inner products are retained explicitly. The following sections
prove the actual few-links count and individual cancellation bounds; their
joint Fourier-energy assembly remains.

## Full spatial and operator assembly of the inverse series

The actual polynomial differential operators are expanded by the finite
Leibniz rule. Each branch is a real scheduled symbol multiplied by an actual
bounded spatial polynomial. The inverse-distance series converges uniformly
on the separated carrier discs, and its coefficients satisfy

$$
\sum_n |\gamma_{j,n}|\le\left(\frac{\sqrt2}{D}\right)^j,
\qquad D=\lVert x_0-y_0\rVert.
$$

The printed Step 0 bound 2/D≤6·2ᵃ fails in the prepared root case a=0,
D=1/4. The proved sharper coefficient bound repairs this numerical step:

$$
2/D=8>6,\qquad \sqrt2/D=4\sqrt2<6.
$$

The prepared root and separated cells therefore both have the needed
coefficient scale 6·2ᵃ. Actual Fubini and summability prove that the full
inverse-circle integral equals a genuine countable Fourier series. The true
branch symbols for an initial mask product have order at most 2T.
On the actual frequency window, nonnegative summable majorants satisfy

$$
|c_n(r)|\le a_n,\qquad
\sum_n a_n\le\sum_{j<T}q^j\le11/10,\qquad
q\le2^{-7\varepsilon N/8}.
$$

This completes the spatial and operator expansion in Step 2 of Estimate 7.5.
Its final distance-transform error and frequency-energy assembly remain.

## Complete weighted linearization: Estimate 7.7

For the actual separated a-cells and occupied p-cell descendants, with
2p>a+t, the exact norm Taylor identity gives error at most 2⁻ᵗ/1000.
Four-point distance collisions thus imply the corresponding doubled-width
projection collision. The actual passing projection test gives the one-cell
raw collision bound 4B times the squared product of cell masses, where

$$
B=2^{-(t-p)}2^{N(k_p[p,t]+6\varepsilon)}.
$$

A witness in a retained cell pair implies that every point of that cell pair
passes the shorter test lists at the next width. This uses genuine direction
motion and the proved width gap. Exact measure sums over retained cells then
allow grouping by their center distances. The true nine-neighbor group graph
and scalar binning bounds give factors 108 and 9.

The singular weight d⁻¹ᐟ² contributes the exact ratio 22. Hence

$$
22\cdot108\cdot9=21384\le2^{\varepsilon N},
$$

and the actual weighted recurrence is

$$
D_{X,Y}^{I,i}(t)\le
2^{N(k_p[p,t]+7\varepsilon)}D_{X,Y}^{J,i+1}(p).
$$

Here J is contained in I, its tests are anchored at depth at most p,
and a+length≤p. The manuscript's stronger length bound (p−a)/2 satisfies
this condition. No collision or energy estimate is supplied as a hypothesis.

## Actual nonzero-symbol links and the graph degree

A nonzero built symbol automatically lies on its occupied anchor carrier.
Its mask derivative factors provide a genuine passing witness at the next
width. Combined with the actual smoothed arc, this selects the contributing
fine-cell columns.

Within each g-ancestor group, all linked first-cell centers lie in the
passing witness's tube. The exact directional count gives at most
2ᴺ⁽ʰᵉⁱᵍʰᵗ⁺⁶ᵋ⁾ centers per group. There are at most 2²ᵋᴺ groups.
For a fixed first cell, the actual second-cell linking coordinates give the
lattice bound 81·2³ᵋᴺ. This bound uses a square containing the rotated center
region; it is coarser than the printed constant 16. The same final exponent
holds because 81≤2ᵋᴺ:

$$
\deg(\alpha)\le
2^{2\varepsilon N}2^{N(k_p[g,p]+6\varepsilon)}
81\,2^{3\varepsilon N}\le2^{N(k_p[g,p]+12\varepsilon)}.
$$

The integrated Schur estimate retains cancellation after each unlinked
integral:

$$
\int\left\|\sum_\alpha Z_\alpha\right\|^2\le
n\sum_\alpha\int\|Z_\alpha\|^2+
\sum_{\alpha\not\sim\beta}
\left|\int\langle Z_\alpha,Z_\beta\rangle\right|.
$$

The actual Fourier amplitude on a parent is the finite sum over its occupied
descendants; omitted zero-mass cells contribute exactly zero.

## Actual angular and radial cancellation

The true support of each arc cutoff within the period centered on that arc
has Lebesgue length at most 2ℓ. This is proved from its chord bound 3ℓ/4
and the sine Taylor inequality. Periodic integration by parts uses this
support mass, preserving the small-arc factor when summing over arcs.

For the actual angular amplitude χ·b(x,·)·b(x′,·), the proved derivative
scale satisfies

$$
M_a\le1024T^2(N^2+1)2^{v-p+\varepsilon N}.
$$

An angular linking failure gives an open neighborhood of the true support
where the phase derivative is bounded below by rτ/3. Actual cell geometry,
r≥2ᵛ⁻², and ParameterFacts yield

$$
\left|\int e^{-irw\cdot(x-x')}\chi(w)b(x,w)b(x',w)\,dw\right|
\le2\ell\,2^{-90N}.
$$

The literal radial amplitude is h(r)=2⁻ᵛΨ(r/2ᵛ)r², supported in
[2ᵛ⁻²,2ᵛ⁺²]. Its actual derivatives obey

$$
|h^{(j)}(r)|\le16\,2^v(512T^2/2^v)^j\quad(j\le6T).
$$

For a radial linking failure, the actual linear-phase integral is bounded
by 2⁻³⁰⁰ᴺ. The full joint integral, arc sum and normalized F recurrence
are now assembled, as detailed below.

## Actual terminal-tree budgets and the near-cell space split

All actual terminal visits retain their multiplicity in the recurrence tree.
The proved short-leaf estimate and tree-size budget give

$$
\mathcal T_{\mathrm{terminal}}\le
2^{N(-V(\mathrm{root})+226\kappa)}.
$$

The actual sum of weighted 2⁻²⁵ᴺ node errors is at most 2⁻²⁰ᴺ.
Together they satisfy the bound with 227κ. These results estimate genuine
state energies and visits; the analytic recurrence controlling the initial
state remains to be assembled.

For the near part of the full space split, true dyadic lattice boxes contain
exactly 81 centers within the needed coordinate range. Thus the actual
pair-cell near relation is symmetric and has row and column degrees at most

$$
81^2=6561.
$$

The complete far part of Estimate 7.8 still needs its two sign combinations
and the scalar binning kernel assembled with the actual circular formula.

## Actual Mattila shell estimate and its state consequence

The true spatial inverse-circle series is integrated against the literal
filtered distance measure. Its weighted coefficient sum is at most 11/10.
Circular Cauchy–Schwarz then bounds the series square by 121/50 times the
actual carrier mass product and the built-symbol Fourier supremum.
The exact stationary prefactor and both Fourier signs give

$$
\operatorname{Shell}_v(\beta)\le
2\rho_1(X)\rho_2(Y)\,F^{\mathrm{sup}}_{X,Y}(v)
+2^{-390N}\bigl(\rho_1(X)\rho_2(Y)\bigr)^2.
$$

On actual occupied separated dyadic cells, every ball separation,
common arc, inverse coefficient and terminal-distance hypothesis is derived
from the cell geometry. Normalizing by the actual positive carrier masses
proves the dyadic shell form of Estimate 7.5. Reached-test contraction bounds
each actual high shell by twice the actual Fourier state at start a, plus
the same terminal error. Thus the low/high recurrence, before refinement to
its split point, is

$$
D_i(a,t)\le320D_{i+1}(a,t-\delta)
+640\sum_{t-\delta<v\le t}F_i(a,t,a,v)
+320\delta\,2^{-390N}.
$$

## Complete actual orthogonality estimate

The true radial density h(r)=2⁻ᵛΨ(r/2ᵛ)r² defines a finite measure. Its
product with two circle arc-length measures is the literal integration
measure for the squared pair amplitude. Carrier mass cancels the spectrum
normalization, including when a carrier has mass zero.

For each arc pair, the square-root-weighted parent amplitude is exactly the
sum over genuinely active occupied fine-cell pairs. The actual complex
cross integral equals the four-point spatial integral of the oscillatory
kernel, by integrable Fubini. Its real inner-product integral inherits the
proved cancellation. All three linking failures give

$$
|\text{unlinked cross integral}|\le
64\,4^v(2\ell)^2 2^{-90N}
\rho(P)\rho(P')\rho(Q)\rho(Q').
$$

The arc count satisfies M·2ℓ≤16. Genuine descendant mass sums and v≤N give
M²·64·4ᵛ(2ℓ)²·2⁻⁹⁰ᴺ≤2⁻⁸⁰ᴺ. Integrated Schur and the exact arc partition
therefore prove the full source Estimate 7.6:

$$
F_{X,Y}(v)\le2^{N(k_p[g,p]+12\varepsilon)}
\sum_{P\subseteq X,\ Q\subseteq Y}
\frac{\rho(P)\rho(Q)}{\rho(X)\rho(Y)}F_{P,Q}(v)+2^{-80N}.
$$

The sum is over the actual occupied p-cell descendants, with the same
literal built symbols. No Fourier or cancellation bound is assumed.

## Actual far-cell space-splitting foundations

A genuine far cell pair has max point separation greater than
(5/2)·2⁻ʰ. In the two-large-pairs case, both point separations exceed
(5/4)·2⁻ʰ. Literal source distance bins imply actual cell separation and
actual regrouping depths a<n<h+12.

The true circle integral has its full two-sign stationary expansion.
Every nonzero stationary coefficient supplies a genuine next-level passing
pair through the literal derivative-branch expansion and antipodal tests.
For the actual cutoff-normalized radial moment, twice-integrated phase
cancellation gives the explicit source envelope

$$
|\mathcal M_{j,j'}(\delta)|\le
\frac{12544\,(j+j'+2)^2\,4^{j+j'+1}
2^{v(1-j-j')}}{(1+2^v|\delta|)^2}.
$$

These are checked analytic and geometric components. Their coefficient sums,
sign cases and depth regrouping still need assembly for full Estimate 7.8.

## Actual induction Moves 1--3

The right split contributes the actual projection test to the parent list.
Every child test has its literal anchor and length inside the shorter
interval, so full Estimate 7.7 gives

$$
D_i(a,t)\le R^{k_p[p,t]+7\varepsilon}D_{i+1}(a,p).
$$

For a left split, the true high shells first use Mattila inversion and then
orthogonality at the constructed split point. The numerical budget absorbs
640 into one tolerance exponent and the finite shell errors into R⁻²⁵:

$$
D_i(a,t)\le320D_{i+1}(a,t-\delta)
+R^{k_p[a,p]+13\varepsilon}\sum_{t-\delta<v\le t}F_i(a,t,p,v)+R^{-25}.
$$

When a remaining test is longest and its symmetric interval is large,
its actual origin supplies the tube test and geometric hypotheses.
Orthogonality and the true profile-height comparison give

$$
F_i(b,e,a,v)\le R^{k_p[a,p]+12\varepsilon}F_i(b,e,p,v)+R^{-25}.
$$

These are proved inequalities for actual analytic states. The finite child
recurrences retain all longest-test ties.

## Genuine weighted tree telescope

Appending a true transition multiplies the actual path coefficient by its
Table 1 coefficient. A discrepancy child advances the mask level once;
a Fourier child keeps it. The proved append identities identify the
weighted child sum with the exact local recurrence contribution.

The multiset levels preserve every path when branches meet. Summing each
local inequality over a level and telescoping through the derived finite
cutoff gives

$$
\mathcal E_{\mathrm{root}}\le
\mathcal T_{\mathrm{terminal}}+\mathcal T_{\mathrm{errors}}.
$$

The already proved terminal and error bounds then give

$$
\mathcal E_{\mathrm{root}}\le R^{-V(\mathrm{root})+227\kappa}.
$$

This last implication explicitly requires the outstanding full
space-splitting recurrence. Moves 1--3 and all tree bookkeeping are proved;
the hypothesis for Move 4 has not yet been discharged. No such analytic
hypothesis is added to Theorem 1.1.

## Full annulus and exact original-piece mixture

The prepared-ball Mattila estimate holds on the full symmetric frequency
annulus [2⁽ᵛ⁻¹⁾, 2⁽ᵛ⁺¹⁾], with both signs. Literal Fourier Cauchy--Schwarz
bounds each retained-piece cross energy by the geometric mean of its true
self energies. Full-mass carrier identities place those self energies on
the actual unit square.

The single global filtered distance measure is exactly the finite mixture
of local filtered measures, with the original retained-piece masses.
Their total mass is at most one, so actual Fourier Cauchy--Schwarz introduces
no loss from the number of types. For the actual 8T masks,

$$
\operatorname{Annulus}_N(\alpha_N)\le
2\left(\sum_t m_t\sqrt{F_t}\right)
\left(\sum_u m_u\sqrt{F_u}\right)+2^{-390N}.
$$

Here Fₜ is the actual built-symbol self-energy supremum and mₜ is the
original piece mass. The identity is generic in the smooth mask order;
the analytic specialization uses 8T to match the finite derivative budget.
Actual mass-loss bounds are available for this same filter order.

## Opposite-sign kernel and near Schur assembly

Literal stationary coefficients have their proved geometric scale bound.
The genuine double order sum is at most 100. Combined with the twice
integrated radial moment, the actual opposite-sign series satisfies

$$
|\mathcal K_{\mathrm{opp}}|\le
\frac{2^{25}\,2^v}{\sqrt{d_xd_y}(1+2^v|d_x-d_y|)^2}
\mathbf1_{Z_{i+1}}(x,x')\mathbf1_{Z_{i+1}}(y,y').
$$

The indicators are the actual next-level passing pair sets, derived from
nonzero built-symbol coefficients. Equal-sign radial moments also have
literal repeated linear-phase decay.

The near relation has actual symmetric degree at most 81². Integrated
Schur gives the real mass-weighted parent Fourier energy bounded by 81²
times its genuine fine-cell energies plus the actual far cross integrals.
The remaining sign and remainder estimates and scalar collision regrouping
must still control those far cross integrals.

## Actual entry estimate and conditional reconstruction

The retained root self energy now has a proved jump to the actual entry
state. With the true entry depth c and original gain parameter beta,

$$
F_t\le R^{\beta+\kappa+12\varepsilon}
\mathcal E_0(c,N,c,N)+R^{-80}.
$$

The actual tree and gauge budget, conditional only on the remaining
space-splitting recurrence for that retained probability, give

$$
\mathcal E_0(c,N,c,N)\le R^{-2\beta+227\kappa+2/N}.
$$

Weakening 227 to the source's 300 and closing the exact original-mass
mixture proves the genuine full symmetric annulus estimate

$$
\operatorname{Annulus}_N(\alpha_N)\le R^{-\beta/3}.
$$

The exact 8T filters have proved domination, finite mass and summable
removed mass. The closed dyadic shells agree with the full annuli almost
everywhere. Stretched-gain summability and the proved reconstruction lemma
then give absolute continuity of the original weighted distance measure.
This entire final chain still explicitly depends on actual Move 4 at each
retained piece and scale; that analytic input is not yet discharged.

## Exact two-circle stationary main product

The actual full-circle stationary main is the literal sum of its two
signs with their square-root prefactor. Its radial product uses

$$
\sqrt{\frac{2\pi}{rd_x}}\sqrt{\frac{2\pi}{rd_y}}r
=\frac{2\pi}{\sqrt{d_xd_y}}.
$$

The opposite phases cancel their quarter-circle constants; the equal
phases contribute respectively i and minus i. Finite expansion and
integrability of the actual cutoff-normalized integer powers prove

$$
\int_{\mathbb R}2^{-v}\Psi(r/2^v)r^2 M_x(r)M_y(r)\,dr
=\mathcal K_{\mathrm{opp}}+\mathcal K_{\mathrm{equal}}.
$$

Every term has the literal radial exponent 1-j-k. The opposite series
is exactly the already bounded passing collision kernel; the two equal
series have moments at d_x+d_y and minus that sum. No stationary-product
identity or energy inequality is assumed as a hypothesis in this step.

## Actual equal-sign source decay

Repeated linear cancellation applies to both genuine sum-distance
moments. The scaled stationary coefficients are at most the geometric
sequence (1/4) to their respective orders. For the actual parameter
budget the radial cancellation ratio satisfies

$$
\left(\frac{1200T^2}{2^v d_x}\right)^T\le R^{-450}.
$$

The common coefficient and radial prefactor is at most R to the fifth
power, and each complete equal-sign term is at most R to minus 400.
The actual count of the two finite double series obeys

$$
2T^2\le R,\qquad |\mathcal K_{\mathrm{equal}}|\le R^{-390}.
$$

These are proved for the actual built symbols under the literal far
geometry and parameter hypotheses. All declarations in the exact
main-product and equal-sign modules have been checked for standard axiom
dependencies only.

## Remaining proof obligations and verification

Estimates 7.5, 7.6 and 7.7, actual Moves 1--3, exact mixture identities and
the genuine weighted tree telescope are proved. Full Estimate 7.8, the
the source shell decay and final reconstruction are proved conditionally
on its remaining actual recurrence. The main target's sole hole is absolute continuity of its actual
prepared weighted distance source.

The hosted check on public commit 886a9d8 compiled the development in
3895 jobs and audited 784 declarations. Only the main theorem used
sorryAx. Sandboxed Comparator built the export in 3892 jobs and rejected
that same forbidden axiom. No successful independent proof replay is
claimed. Later source changes require a new run.

Palomar registration remains pending the completed proof, successful
verification of the exact public commit, truthful metadata and registry
review.
