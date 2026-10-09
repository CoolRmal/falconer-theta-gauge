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
Numerical inverse norms and the full periodic circular expansion remain.

## Remaining proof obligations

The manuscript's proof still requires the full periodic circular stationary
expansion, numerical inverse-operator
norms, and four uniform energy recurrences and their shell assembly. Fixed-parameter theorems cannot be used at
scale-dependent parameters without proving the needed uniform dependence.

The main target now uses the proved preparation and the actual weighted
distance carrier. Its one explicit hole is absolute continuity of the
weighted distance source. Comparator permits only
`propext`, `Quot.sound`, and `Classical.choice`, so it must reject the current
target's dependence on `sorryAx`. Registration on Palomar requires the completed
proof, successful verification of the exact public commit, truthful metadata,
and the registry review. None of those later statuses is asserted here.
