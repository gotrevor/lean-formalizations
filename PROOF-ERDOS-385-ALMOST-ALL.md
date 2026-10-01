# Erdős #385: $F(n) = n + (1+o(1))\sqrt n$ for almost all $n$

Draft 1, 2026-10-01.  Unrefereed (one self-referee pass, §8).  Companion to
`DOOR-ALMOSTALL-ERDOS-385.md` (outline + source checks) and `LIT-ERDOS-385.md` (prior art).
Overall confidence that the proof is correct as written: **~80%** (§8 lists the soft spots).

## 0. Statement

For $n \ge 5$ let
$$F(n) = \max\{ m + p(m) : m < n,\ m \text{ composite} \},$$
where $p(m)$ is the least prime factor of $m$.  For composite $m < n$ we have $p(m) \le \sqrt m < \sqrt n$,
so trivially $F(n) < n + \sqrt n$.

**Theorem A.**  Fix $\delta \in (0, 1/4)$ and $\varepsilon > 0$.  Then
$$\#\{ n \le Y : F(n) < n + (1-\delta)\sqrt n \} \ll_{\delta,\varepsilon} Y \exp\!\big(-(\log Y)^{1/3-\varepsilon}\big).$$

**Corollary B.**  There is a function $\delta(n) \to 0$ and a set $\mathcal E \subset \mathbb N$ of
asymptotic density $0$ such that $F(n) \ge n + (1-\delta(n))\sqrt n$ for all $n \notin \mathcal E$.
Hence $F(n) = n + (1+o(1))\sqrt n$ for almost all $n$, and in particular $F(n) - n \to \infty$ along a
density-one set.

Context.  Tao (blog, 2024-08-19, in a reply) remarked that "almost all $n$ have $F(n) = n + n^{1/2+o(1)}$"
should be within reach.  Theorem A is the sharper $(1 - \delta)\sqrt n$ form.  It says nothing about
#385(i) or #385(ii) for every $n$: a variance bound controls only the measure of the exceptional set.

## 1. External inputs (quoted)

**(MVT) Mean value theorem.**  Matomäki–Radziwiłł, *Multiplicative functions in short intervals*,
Annals 2016, arXiv:1501.04585 (hereafter MR16), **Lemma 6**, verbatim: "Let $A(s) = \sum_{n\le N} a_n n^{-s}$.
Then $\int_{-T}^{T} |A(it)|^2\,dt = (T + O(N)) \sum_{n \le N} |a_n|^2$.  Proof.  See [IK, Theorem 9.1]."
We use only the upper bound.

**(PAR) Parseval bound for short sums.**  MR16 **Lemma 14**, verbatim:

> Let $|a_m| \le 1$.  Assume $1 \le h_1 \le h_2 = X/(\log X)^{1/5}$.  Consider, for $X \le x \le 2X$,
> $S_j(x) = \sum_{x \le m \le x + h_j} a_m$ and write $A(s) := \sum_{X \le m \le 4X} a_m m^{-s}$.  Then
> $$\frac1X\int_X^{2X}\Big|\frac{1}{h_1}S_1(x) - \frac1{h_2}S_2(x)\Big|^2 dx \ll \frac{1}{(\log X)^{2/15}} + \int_{1+i(\log X)^{1/15}}^{1+iX/h_1}|A(s)|^2|ds| + \max_{T \ge X/h_1}\frac{X/h_1}{T}\int_{1+iT}^{1+2iT}|A(s)|^2|ds|.$$

The general-parameter form we use is in print as Teräväinen, *Almost primes in almost all short
intervals*, arXiv:1510.06005, **Lemma 1** (with $2 \le h_1 \le h_2 \le X/T_0^3$, $T_0 \ge 1$; first term
$1/T_0$; lower limit of the first integral $T_0$).  His proof reads, verbatim: "This is Lemma 14 in the
paper [15] (except that we do not specify the value of $T_0$)."  We therefore use:

> **(PAR′)**  Let $|a_m| \le 1$ be real, supported on $[X, 4X]$, $T_0 \ge 1$, $2 \le h_1 \le h_2 \le X/T_0^3$.
> With $S_j$ and $A$ as above,
> $$\frac1X\int_X^{2X}\Big|\frac{S_1(x)}{h_1} - \frac{S_2(x)}{h_2}\Big|^2 dx \ll \frac1{T_0} + \int_{T_0}^{X/h_1}|A(1+it)|^2 dt + \max_{T\ge X/h_1}\frac{X}{h_1 T}\int_T^{2T}|A(1+it)|^2 dt,$$
> with an absolute implied constant.

Two transcription notes.  (a) Teräväinen writes $F(s) = \sum_{n \sim X}$ ($X \le n < 2X$) and normalises
$S_h$ by $1/h$ twice (a typo); his proof is MR's, which uses the $[X, 4X]$ support.  Our coefficients
are supported in $[X, 2X)$ (§2), so both normalisations apply.  (b) Teräväinen's statement omits
$|a_n| \le 1$.  It is needed (MR's proof bounds $|A(1+it)| \le \sum |a_m|/m \ll 1$ in the low-frequency
part), and our coefficients satisfy it.  Where the parameters enter MR's proof: only in the bound
$|U_1/h_1 - U_2/h_2| \ll T_0^2 h_2/X$ for the part $|t| \le T_0$ of Perron's formula (MR16 p. 22,
quoted: "$\frac1{h_1}U_1(x) - \frac1{h_2}U_2(x) \ll T_0^2 x \frac{h_2}{X^2}$").  With $h_2 \le X/T_0^3$
this is $\le 1/T_0$, giving the first term.

**(VK) Smoothed prime sums.**  MR16, proof of **Lemma 11**, equation (15) and the display after it.  For
a smooth compactly supported $f$ with Mellin-type transform $\tilde f$ satisfying
$\tilde f(x+iy) \ll_{A,B} (1+|y|)^{-B}$ for $|x| \le A$:
$$\sum_n \Lambda(n) n^{it} f\Big(\frac nP\Big) = -\frac1{2\pi i}\int_{2-i\infty}^{2+i\infty}\tilde f(s)\frac{\zeta'}{\zeta}(s-it)\frac{P^s}{s}\,ds \quad (15)$$
"We truncate the integral at $|t| = T$ ... shift the contour to $\sigma = 1 - c(\log T)^{-2/3+\varepsilon}$,
staying in the zero-free region of the $\zeta$-function, and use [Ivić (1.52)] ... It follows that (15) is
equal to
$$\frac{\tilde f(1+it)}{1+it}\cdot P^{1+it} + O\Big(P\exp\Big(-\frac{\log P}{(\log T)^{2/3+\varepsilon}}\Big)(\log T)^2\Big)."$$
MR apply this with $t$ replaced by differences $t - t'$ of points in $[-T, T]$, and with one specific $f$.
The derivation uses only that $f$ is smooth and compactly supported in $(0,\infty)$ (through the decay of
$\tilde f$); the implied constant depends on $f$ and $\varepsilon$.  We use it for $|t| \le T$, one
fixed $f$ depending only on $\delta$, and both signs of $t$.  ⚠️ This is a displayed step, not a numbered
lemma (see §8, item 1).

**(PNT) Prime number theorem with classical error.**  $\psi(y) = y + O(y\exp(-c\sqrt{\log y}))$ for an
absolute $c > 0$ (de la Vallée Poussin; e.g. Davenport, *Multiplicative Number Theory*, ch. 18).  Consequence
used: for $y \ge y_0$ and $y \exp(-4(\log y)^{1/3}) \le H \le y$,
$$\pi(y + H) - \pi(y) \ge \frac{H}{2\log(2y)},$$
since the error $O(y e^{-c\sqrt{\log y}})$ is $o(H)$ and prime powers contribute $O(\sqrt{y}\log y)$.
(Not re-opened this session; textbook.)

## 2. Set-up

Fix $\delta \in (0,1/4)$.  Fix once and for all a smooth $g : (0,\infty) \to [0,1]$ with
$$\operatorname{supp} g \subset [1-\tfrac{\delta}{2},\, 1-\tfrac{\delta}{4}],\qquad g = 1 \text{ on } J_\delta := [1-\tfrac{7\delta}{16},\, 1-\tfrac{5\delta}{16}].$$
All implied constants below may depend on $\delta$ (through $g$) and on $\varepsilon$, nothing else.

Let $Z$ be large and put
$$X = (1-\tfrac\delta2)Z,\quad h = \tfrac{\delta}{4}\sqrt Z,\quad h_1 = \lfloor h/2 \rfloor - 1,\quad T_0 = \exp((\log Z)^{1/3}),\quad h_2 = X/T_0^3 .$$

**Coefficients.**  For $m \ge 1$ let
$$a_m = \frac{1}{\log Z}\sum_{\substack{m = pq\\ p,\,q \text{ prime},\ \sqrt Z \le q \le (1+2\delta)\sqrt Z}} (\log p)\, g\Big(\frac{p}{\sqrt Z}\Big).$$
Facts:

1. *Unique representation, size.*  If $a_m \ne 0$ then $m = pq$ with $p \le (1-\delta/4)\sqrt Z < \sqrt Z \le q$,
   so $p < q$ are distinct and $p = p(m)$ is determined by $m$.  Hence $0 \le a_m \le \frac{\log\sqrt Z}{\log Z} = \frac12$.
2. *Support.*  $m \ge (1-\frac\delta2)\sqrt Z\cdot\sqrt Z = X$ and $m \le (1-\frac\delta4)(1+2\delta)Z \le (1+\frac{7\delta}{4})Z < 2X$
   (as $\delta < 1/4$: $2X = (2-\delta)Z$ and $1 + \frac{7\delta}4 < 2 - \delta$).  So $\operatorname{supp} a \subset [X, 2X) \subset [X,4X]$.
3. *Factorisation.*  $A(s) := \sum_m a_m m^{-s} = \frac{1}{\log Z}\, P(s)\, Q(s)$ with
   $$P(s) = \sum_{p} (\log p)\, g(p/\sqrt Z)\, p^{-s},\qquad Q(s) = \sum_{\sqrt Z \le q \le (1+2\delta)\sqrt Z} q^{-s},$$
   by fact 1 (every product $pq$ arises once).

With $S_j(x) = \sum_{x \le m \le x + h_j} a_m$ as in (PAR′), $j = 1,2$.

## 3. Reduction: a witness gives the margin

**Lemma 1.**  Let $Z$ be large and $n \in [Z + h,\ (1+\frac\delta2)Z]$.  If $a_m > 0$ for some
$m \in [n-h, n-1]$, then $F(n) \ge n + (1-\delta)\sqrt n$.

*Proof.*  Write $m = pq$ as in fact 1.  Then $m$ is composite, $m < n$, and $p(m) = p \ge (1-\frac\delta2)\sqrt Z$.
So
$$F(n) \ge m + p \ge n - h + p \ge n + (1 - \tfrac\delta2 - \tfrac\delta4)\sqrt Z = n + (1-\tfrac{3\delta}4)\sqrt Z.$$
Since $n \le (1+\frac\delta2)Z$ and $\sqrt{1+\delta/2} \le 1 + \delta/4$,
$(1-\delta)\sqrt n \le (1-\delta)(1+\frac\delta4)\sqrt Z = (1 - \frac{3\delta}{4} - \frac{\delta^2}{4})\sqrt Z$.  $\square$

**Lemma 2 (from $n$ to $x$).**  Let $\mathcal B_Z$ be the set of integers $n \in [Z+h, (1+\frac\delta2)Z]$ with
$F(n) < n + (1-\delta)\sqrt n$, and let $\mathcal V_Z = \{x \in [Z, (1+\frac\delta2)Z] : S_1(x) = 0\}$.  Then
$\#\mathcal B_Z \le (1 + 2/h)\,\mathrm{meas}(\mathcal V_Z) \le 2\,\mathrm{meas}(\mathcal V_Z)$ for $Z$ large.

*Proof.*  Let $n \in \mathcal B_Z$ and $x \in [n-h, n-h/2]$.  Then $[x, x+h_1] \subset [n-h, n-1]$, so by
Lemma 1 every $m$ in it has $a_m = 0$, i.e. $S_1(x) = 0$; also $x \in [Z, (1+\frac\delta2)Z]$.  So
$[n-h, n-h/2] \subset \mathcal V_Z$.  Integrating, $\frac h2\#\mathcal B_Z \le \int_{\mathcal V_Z}\#\{n : x \in [n-h, n-h/2]\}\,dx \le (\frac h2 + 1)\,\mathrm{meas}(\mathcal V_Z)$.  $\square$

## 4. The long average is large

**Lemma 3.**  For $x \in [Z, (1+\frac\delta2)Z]$ and $Z$ large, $\dfrac{S_2(x)}{h_2} \ge \mu_Z := \dfrac{c_1\delta}{\log^2 Z}$,
with $c_1 > 0$ absolute.

*Proof.*  $S_2(x) = \frac1{\log Z}\sum_p (\log p)\,g(p/\sqrt Z)\cdot\#\{q \text{ prime}: x/p \le q \le (x+h_2)/p,\ \sqrt Z \le q \le (1+2\delta)\sqrt Z\}$.
For $p \in \operatorname{supp} g(\cdot/\sqrt Z)$: $x/p \ge Z/((1-\frac\delta4)\sqrt Z) > \sqrt Z$, and
$(x + h_2)/p \le \frac{1+\delta/2}{1-\delta/2}\sqrt Z\,(1+o(1)) \le (1+\frac{8\delta}{7})\sqrt Z(1+o(1)) < (1+2\delta)\sqrt Z$
(using $\delta \le 1/4$).  So the $q$-range constraint is automatic and the inner count is
$\pi(y + H) - \pi(y)$ (up to endpoints) with $y = x/p \in [\sqrt Z, 2\sqrt Z]$ and
$H = h_2/p \ge \frac{X}{T_0^3\sqrt Z} \ge y\cdot\frac{1}{4T_0^3}$.  As $\log Z \le 2\log y + O(1)$,
$4T_0^3 = 4\exp(3(\log Z)^{1/3}) \le \exp(4(\log y)^{1/3})$ for large $Z$.  By (PNT) the count is
$\ge H/(2\log(2y)) \ge h_2/(2p\log(4\sqrt Z))$.  Hence
$$S_2(x) \ge \frac{h_2}{2\log Z\,\log(4\sqrt Z)}\sum_{p/\sqrt Z \in J_\delta}\frac{\log p}{p} \ge \frac{h_2}{\log^2 Z}\cdot\frac{1}{2}\log\frac{1 - 5\delta/16}{1-7\delta/16},$$
using Mertens' $\sum_{a < p \le b}\frac{\log p}{p} = \log\frac ba + o(1)$ (a consequence of (PNT)) and
$\log\frac{1-5\delta/16}{1-7\delta/16} \ge \frac{\delta}{8}$.  $\square$

## 5. The Dirichlet polynomial is small on $[T_0, 8X]$

**Lemma 4.**  For $T_0 \le |t| \le 8X$ and any $\varepsilon > 0$,
$$|P(1+it)| \ll_{\delta,\varepsilon} \eta_Z := \exp\big(-(\log Z)^{1/3-\varepsilon}\big).$$

*Proof.*  Let $g_0(u) = g(u)/u$, smooth with the same support.  Then
$$P(1+it) = \sum_n \Lambda(n)\, g\Big(\frac{n}{\sqrt Z}\Big)n^{-1-it} - \sum_{k\ge2}\sum_{p}(\log p)\,g\Big(\frac{p^k}{\sqrt Z}\Big)p^{-k(1+it)},$$
where the second sum removes the prime powers $p^k$, $k \ge 2$, in the support (this identity is exact,
since $P$ runs over primes only).  The $k \ge 2$ part has $O(Z^{1/4}\log Z)$ terms, each
$\ll \log Z/\sqrt Z$, so it is $\ll Z^{-1/4}\log^2 Z$.  For the main part,
$$\sum_n \Lambda(n) g\Big(\frac n{\sqrt Z}\Big) n^{-1-it} = \frac{1}{\sqrt Z}\sum_n \Lambda(n)\, n^{-it} g_0\Big(\frac{n}{\sqrt Z}\Big).$$
Apply (VK) with $f = g_0$, $P = \sqrt Z$, $t \to -t$, $T = 16Z \ge 8X$:
$$\frac{1}{\sqrt Z}\Big[\frac{\tilde g_0(1-it)}{1-it}\,\sqrt Z^{\,1-it} + O\Big(\sqrt Z\exp\Big(-\frac{\log\sqrt Z}{(\log 16Z)^{2/3+\varepsilon}}\Big)\log^2(16Z)\Big)\Big].$$
The first term is $\ll_B (1+|t|)^{-B} \le T_0^{-1}$ for $|t| \ge T_0$ (take $B = 1$).  The second is
$\ll \exp(-\frac13(\log Z)^{1/3-\varepsilon})\log^2 Z$.  All three contributions are $\ll \eta_Z$ after
renaming $\varepsilon$.  $\square$

**Lemma 5 (mean square of $Q$).**  For $U \ge 1$, $\int_{-U}^{U}|Q(1+it)|^2 dt \ll \dfrac{U + \sqrt Z}{\sqrt Z \log Z}$.

*Proof.*  (MVT) with $a_n = 1/n$ on primes $n = q \in [\sqrt Z, (1+2\delta)\sqrt Z]$, $N = 2\sqrt Z$:
$\int_{-U}^U |Q(1+it)|^2 = (U + O(\sqrt Z))\sum_q q^{-2}$, and $\sum_q q^{-2} \le \pi(2\sqrt Z)/Z \ll 1/(\sqrt Z\log Z)$.  $\square$

## 6. The variance

**Proposition 6.**  With the parameters of §2,
$$\mathcal D := \frac1X\int_X^{2X}\Big|\frac{S_1(x)}{h_1} - \frac{S_2(x)}{h_2}\Big|^2dx \ll_{\delta,\varepsilon} \exp\big(-(\log Z)^{1/3-\varepsilon}\big).$$

*Proof.*  Check (PAR′): $|a_m| \le 1/2$, real, support in $[X, 4X]$ (fact 2), $T_0 \ge 1$,
$2 \le h_1 \le h_2 = X/T_0^3$ for large $Z$.  The three terms:

1. $1/T_0 = \exp(-(\log Z)^{1/3})$.
2. $\int_{T_0}^{X/h_1}|A(1+it)|^2dt \le \frac{1}{\log^2 Z}\sup_{T_0\le|t|\le X/h_1}|P(1+it)|^2\int_{-X/h_1}^{X/h_1}|Q(1+it)|^2dt$.
   Here $X/h_1 \le 16\sqrt Z/\delta \le 8X$, so Lemma 4 applies, and Lemma 5 with $U = X/h_1 \ll \sqrt Z/\delta$ gives
   $\ll \eta_Z^2\,\delta^{-1}(\log Z)^{-3}$.
3. For $X/h_1 \le T \le 4X$: $\frac{X}{h_1T}\int_T^{2T}|A|^2 \le \frac{X}{h_1 T}\cdot\frac{\eta_Z^2}{\log^2 Z}\cdot\frac{2T + O(\sqrt Z)}{\sqrt Z\log Z} \ll \eta_Z^2\delta^{-1}(\log Z)^{-3}$
   (Lemmas 4, 5; $|t| \le 8X$ holds).  For $T > 4X$: by (MVT) applied to $A$ itself (length $\le 2X$),
   $\int_T^{2T}|A(1+it)|^2 \le (2T + O(X))\sum_m a_m^2m^{-2} \ll T/X$, so the term is $\ll 1/h_1 \ll Z^{-1/2}$.

Summing, $\mathcal D \ll e^{-(\log Z)^{1/3}} + \eta_Z^2 + Z^{-1/2} \ll \exp(-(\log Z)^{1/3-\varepsilon})$.  $\square$

## 7. Proof of Theorem A and Corollary B

*Chebyshev.*  For $x \in \mathcal V_Z$ we have $S_1(x) = 0$ and, by Lemma 3, $S_2(x)/h_2 \ge \mu_Z$; so the
integrand of $\mathcal D$ is $\ge \mu_Z^2$ on $\mathcal V_Z \subset [X, 2X]$.  Hence
$$\mathrm{meas}(\mathcal V_Z) \le \frac{X\mathcal D}{\mu_Z^2} \ll_\delta Z\,\frac{\log^4 Z}{\delta^2}\exp(-(\log Z)^{1/3-\varepsilon}) \ll Z\exp(-(\log Z)^{1/3-2\varepsilon}).$$
By Lemma 2, $\#\mathcal B_Z \ll Z\exp(-(\log Z)^{1/3-2\varepsilon})$.

*Covering $[1, Y]$.*  Let $Z_0$ be large and $Z_{j+1} = (1+\frac\delta4)Z_j$.  For large $Z_j$,
$Z_{j+1} + h(Z_{j+1}) \le (1+\frac\delta2)Z_j$, so the ranges $[Z_j + h(Z_j), (1+\frac\delta2)Z_j]$ cover
$[Z_0 + h(Z_0), \infty)$.  For $n$ in such a range with $F(n) < n + (1-\delta)\sqrt n$, $n \in \mathcal B_{Z_j}$.
The ranges meeting $[1, Y]$ have $Z_j \le Y$.  Those with $Z_j \le \sqrt Y$ contribute at most
$\sum_{Z_j \le \sqrt Y}(1+\frac\delta2)Z_j \ll_\delta \sqrt Y$ in total.  Those with $Z_j \in (\sqrt Y, Y]$
each contribute $\ll Z_j\exp(-(\log\sqrt Y)^{1/3-2\varepsilon})$, and $\sum_{Z_j \le Y} Z_j \ll_\delta Y$.
So the count in Theorem A is $\ll_{\delta,\varepsilon} Y\exp(-(\log Y)^{1/3-3\varepsilon}) + Z_0$.  Rename
$\varepsilon$.  $\square$

*Corollary B.*  Let $E_k = \{n : F(n) < n + (1-\frac1k)\sqrt n\}$ ($k \ge 5$), each of density $0$ by
Theorem A.  Choose $N_5 < N_6 < \dots$ with $\#(E_k \cap [1,Y]) \le Y/k$ for all $Y \ge N_k$.  Put
$\delta(n) = 1/k$ for $N_k \le n < N_{k+1}$ and $\mathcal E = \bigcup_k (E_k \cap [N_k, N_{k+1}))$.  For
$N_k \le Y < N_{k+1}$: $\#(\mathcal E \cap [1, Y]) \le \sum_{j < k}\#(E_j\cap[1, N_{j+1}]) + Y/k$; choosing
$N_{k+1}$ also large enough that $\sum_{j\le k}\#(E_j \cap [1, N_{j+1}]) \le N_{k+1}/k$ makes this $\le 2Y/(k-1) \to 0$.
For $n \notin \mathcal E$, $n \in [N_k, N_{k+1})$: $n \notin E_k$, i.e. $F(n) \ge n + (1-\delta(n))\sqrt n$.
With $F(n) < n + \sqrt n$ this is $F(n) = n + (1+o(1))\sqrt n$ off $\mathcal E$.  $\square$

## 7a. Sanity checks (known-boundary siblings)

1. **Single factor gives nothing.**  Run the same argument with $A$ a prime polynomial alone (coefficients
   on primes in $[X, 2X]$, $h_1 \asymp \sqrt X$).  The (MVT) bound for $\int_{T_0}^{X/h_1}|A|^2$ is
   $\asymp (X/h_1 + X)\sum_p p^{-2} \asymp 1/\log X$, versus $\mu^2 \asymp 1/\log^2 X$: no saving.  A
   pointwise VK bound times the length $X/h_1$ also loses.  The saving in §6 comes only from the bilinear
   structure: one factor ($P$) is pointwise small, the other ($Q$) has length $\asymp \sqrt Z \asymp X/h_1$,
   so (MVT) on $Q$ costs only $O(1/\delta)$.  So the argument proves nothing about primes in short
   intervals.  (For the record, "primes in almost all intervals of length $x^{1/2-\varepsilon}$" is TRUE and
   known, Huxley's $x^{1/6+\varepsilon}$; it is not a false sibling, and we do not reprove it.)
2. **Interval length must be $\asymp \sqrt Z$.**  If $h_1 = Z^{1/2-\kappa}$ with $\kappa > 0$, term 2 of §6 becomes
   $\eta_Z^2 Z^{\kappa}/\log^3 Z$, which is not small: the method stops exactly at the scale of the theorem.
   (That smaller scale is "Theorem B" in the DOOR file and genuinely needs large-values input.)  Consistent:
   nothing below the claimed scale is claimed.
3. **Every $n$.**  The output is a measure bound, so it cannot exclude a sparse set of bad $n$; Tao's
   Siegel-zero scenario is untouched.  Consistent with the literature.
4. **Support sanity.**  Requiring both factors $> \sqrt x$ would make $\mu_Z = 0$ (no products $\le x$);
   Lemma 3 fails and nothing is claimed.
5. **Numerics** (`scripts/erdos385-almostall-probe.py 2e7 0.2`, from the DOOR file): the fraction of $n$ in
   $[2^k, 2^{k+1})$ with $(F(n) - n)/\sqrt n < 0.8$ falls from 0.879 ($k = 14$) to 0.318 ($k = 23$), and
   with $< 0.5$ from 0.398 to 0.0003.  Slow, as predicted (witness count per window
   $\asymp \delta^2\sqrt n/\log^2 n$).

## 8. Referee pass (hostile reread)

1. **(VK) is a displayed step, not a numbered lemma.**  MR16 state it inside the proof of Lemma 11, for
   their specific $f$ and for arguments $t - t'$ with $t, t' \in [-T, T]$.  We use it for our $g_0$ and
   $|t| \le T$.  The derivation (Mellin inversion, truncation at height $T$, contour shift into the
   Vinogradov–Korobov zero-free region, Ivić (1.52)) uses only smoothness and compact support of $f$, so the
   transfer is routine, but a referee would want a numbered citation.  Candidates: Iwaniec–Kowalski ch. 8
   (VK region) plus a two-line Mellin argument; or prove it inline.  **Soft spot, 85%.**  Note the
   theorem only needs *some* $o(1)$ pointwise saving beating $\log^4 Z$ (any $\exp(-(\log Z)^{c})$), so even
   a weaker zero-free region (de la Vallée Poussin, giving $\exp(-c\sqrt{\log Z}/\ldots)$ only for
   $|t| \le \exp(\sqrt{\log Z})$) would NOT suffice, because $|t|$ runs up to $\asymp \sqrt Z/\delta$.  VK (or
   any region $1 - c/(\log T)^{1-\kappa}$) is genuinely used.
2. **(PAR′) parameters.**  We rely on Teräväinen's printed Lemma 1, whose proof is MR's.  I checked in MR's
   proof that the parameters enter only through the low-frequency display (quoted in §1).  The $|a_m| \le 1$
   hypothesis is used there and holds.  **OK, 95%.**
3. **Lemma 3's PNT range.**  Needs short-interval PNT for $H \ge y\exp(-4(\log y)^{1/3})$; classical
   de la Vallée Poussin suffices since $\exp(-c\sqrt{\log y}) = o(\exp(-4(\log y)^{1/3}))$.  Endpoint and
   prime-power losses are $O(\sqrt y\log y)$, negligible.  **OK.**
4. **Lemma 4, the $T_0^{-1}$ term vs $\eta_Z$.**  $T_0^{-1} = \exp(-(\log Z)^{1/3}) \le \eta_Z$.  The main term
   $\tilde g_0(1-it)/(1-it)$ decays like $(1+|t|)^{-B}$ for every $B$ with constants depending on $g$, i.e.
   on $\delta$.  **OK.**
5. **Lemmas 2-4 display slips** found on reread (a garbled constant chain, a dangling fraction, a stray
   symbol $R$) were fixed in place.  No mathematical change.
7. **Measure vs integers in Chebyshev.**  $\mathcal V_Z$ is a union of intervals (as $S_1$ is a step function
   of $x$), so it is measurable; fine.
8. **Is the $(1-\delta)$ constant right?**  Lemma 1 gives margin $(1-\frac{3\delta}4)\sqrt Z \ge (1-\delta)\sqrt n$
   on the range.  The witness factor $p \ge (1-\frac\delta2)\sqrt Z$ while the window is $\frac\delta4\sqrt Z$;
   both choices are inside the $\delta$ budget.  **OK.**
9. **Novelty.**  Routine for an expert in the MR/Teräväinen school (85%); not found written (LIT sweep,
   2026-10-01), and sharper than Tao's stated $n^{1/2+o(1)}$.  `papers followups` on 1510.06005 and
   2207.05038 still to run before calling it new in public.

**Overall: ~80% correct as written; the one substantive dependency to firm up is (VK) as a citable lemma.**
