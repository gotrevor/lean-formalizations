# Erdős #385: $F(n) = n + (1+o(1))\sqrt n$ for almost all $n$

Draft 2, 2026-10-01.  One self-referee pass (§8), one independent referee pass (end of file), and a
revision addressing every referee issue (§9).  Companion to `DOOR-ALMOSTALL-ERDOS-385.md` (outline,
source checks, corrected E3 literature Props) and `LIT-ERDOS-385.md` (prior art).
Overall confidence that the proof is correct as written: **~90%** (§9 has the updated soft spots).

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
We use only the upper bound, in the safe form $\int_{-T}^{T}|A(it)|^2dt \le C(T + N)\sum|a_n|^2$ with $C$
absolute (MR print $T + O(N)$ where Montgomery–Vaughan have $2T + O(N)$ over $[-T,T]$; the constant
$C$ absorbs either).

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
> $$\frac1X\int_X^{2X}\Big|\frac{S_1(x)}{h_1} - \frac{S_2(x)}{h_2}\Big|^2 dx \ll \frac1{T_0} + \int_{T_0}^{X/h_1}|A(1+it)|^2 dt + \max_{T\ge X/(2h_1)}\frac{X}{h_1 T}\int_T^{2T}|A(1+it)|^2 dt,$$
> with an absolute implied constant.

Two hygiene points (independent referee, issues 4 and 6).  (i) The printed lemmas allow complex $a_m$
but integrate over $t > 0$ only; MR's proof treats the negative half "completely similarly", which is
valid because $|A(1-it)| = |A(1+it)|$ for **real** $a_m$.  For complex $a_m$ the statement is false
as printed ($a_m = m^{-i\tau}$, see DOOR §"E3 literature Props", control 1a), and the correct form
integrates over $T_0 \le |t| \le X/h_1$ and $T \le |t| \le 2T$.  Our $a_m$ are real.  (ii) MR's
display (19) (re-read in the PDF this revision) gives the tail as $\max_{T \ge X/(2h_j)}$; the
lemma statement prints $T \ge X/h_1$.  We use the weaker threshold $X/(2h_1)$ that the proof
actually delivers.  The $j = 2$ high-frequency part is $(X/h_2)^2\int_{X/h_2}^\infty|A|^2t^{-2}dt$ in
MR's (19); split it at $X/h_1$: the piece on $[X/h_2, X/h_1]$ is $\le \int_{X/h_2}^{X/h_1}|A|^2$, inside
the middle term because $X/h_2 \ge T_0^3 \ge T_0$, and the rest is $\le (h_1/h_2)^2$ times the $j = 1$
part.  A dyadic split of $\int_{X/h_1}^\infty |A|^2t^{-2}$ gives the max over $T \ge X/(2h_1)$.

Two transcription notes.  (a) Teräväinen writes $F(s) = \sum_{n \sim X}$ ($X \le n < 2X$) and normalises
$S_h$ by $1/h$ twice (a typo); his proof is MR's, which uses the $[X, 4X]$ support.  Our coefficients
are supported in $[X, 2X)$ (§2), so both normalisations apply.  (b) Teräväinen's statement omits
$|a_n| \le 1$.  It is needed (MR's proof bounds $|A(1+it)| \le \sum |a_m|/m \ll 1$ in the low-frequency
part), and our coefficients satisfy it.  Where the parameters enter MR's proof: only in the bound
$|U_1/h_1 - U_2/h_2| \ll T_0^2 h_2/X$ for the part $|t| \le T_0$ of Perron's formula (MR16 p. 22,
quoted: "$\frac1{h_1}U_1(x) - \frac1{h_2}U_2(x) \ll T_0^2 x \frac{h_2}{X^2}$").  With $h_2 \le X/T_0^3$
this is $\le 1/T_0$, giving the first term.

**(VKZ) Vinogradov–Korobov zero-free region with a log-derivative bound.**  There are absolute
constants $c_0 > 0$, $C_0$ such that for $T \ge 3$ and
$$\sigma \ge 1 - \frac{c_0}{(\log T)^{2/3}(\log\log T)^{1/3}},\qquad |y| \le T,$$
$\zeta(\sigma+iy) \ne 0$ and $\big|\frac{\zeta'}{\zeta}(\sigma+iy) + \frac{1}{\sigma+iy-1}\big| \le C_0\log T$.
Sources: the zero-free region is Titchmarsh, *The Theory of the Riemann Zeta-Function* (2nd ed.),
Theorem 6.19; the log-derivative bound in (half of) that region follows from Titchmarsh's general
Theorem 3.11 (zero-free region plus growth bound gives $\zeta'/\zeta \ll \phi/\theta$), shrinking $c_0$.
⚠️ Theorem numbers from memory, not re-opened this session (80%); the statement itself is textbook.
The bound $C_0\log T$ is deliberately weaker than the sharp $(\log T)^{2/3}(\log\log T)^{1/3}$.
This replaces the earlier quotation of MR16's proof of Lemma 11, whose contour line
"$\sigma = 1 - c(\log T)^{-2/3+\varepsilon}$" is a typo (independent referee, issue 1): that line lies
*outside* the VK region; MR's own error term is consistent only with exponent $-2/3-\varepsilon$.

**Lemma VK (smoothed prime sums; numbered here, proved below).**  Let $f : (0,\infty) \to \mathbb C$
be smooth with compact support in $[a, b] \subset (0, \infty)$, and let
$\tilde f(s) = \int_0^\infty f(x)x^{s-1}dx$ be its standard Mellin transform.  For every
$\varepsilon > 0$ there is $C = C(f,\varepsilon)$ such that for all $P \ge 2$, $T \ge 3$ with
$P \le T$, and all real $t$ with $|t| \le T/2$:
$$\Big|\sum_n \Lambda(n)\, n^{-it} f\Big(\frac nP\Big) - \tilde f(1-it)\,P^{1-it}\Big| \le C\Big(P\exp\Big(-\frac{\log P}{(\log T)^{2/3+\varepsilon}}\Big)\log T + 1\Big).$$
Note the main term carries **no** factor $1/(1-it)$: MR16's (15) writes $P^s/s$, i.e. a different
normalisation of the transform, and transcribing their main term under the standard Mellin convention
would be false (independent referee, issue 2; DOOR control 3b).

*Proof.*  (a) *Decay.*  Integrating by parts $B$ times, $\tilde f(s) = \frac{(-1)^B}{s(s+1)\cdots(s+B-1)}\int f^{(B)}(x)x^{s+B-1}dx$,
so $|\tilde f(\sigma+iy)| \ll_{f,B} (1+|y|)^{-B}$ uniformly for $\sigma \in [\frac12, 2]$.
(b) *Mellin inversion.*  With $\sigma_0 = 1 + 1/\log P$ and $f(x) = \frac1{2\pi i}\int_{(\sigma_0)}\tilde f(s)x^{-s}ds$,
$$\Sigma := \sum_n \Lambda(n)n^{-it}f(n/P) = \frac1{2\pi i}\int_{(\sigma_0)}\tilde f(s)\,P^s\Big(-\frac{\zeta'}{\zeta}\Big)(s+it)\,ds,$$
the interchange being justified by absolute convergence ($\sum\Lambda(n)n^{-\sigma_0} \ll \log P$ and (a)).
(c) *Truncation.*  On $\sigma_0$, $|P^s| = eP$ and $|\zeta'/\zeta(s+it)| \le \frac{1}{\sigma_0-1} + O(1) \ll \log P$.
By (a) with $B = 3$ the part $|\mathrm{Im}\,s| > T$ is $\ll_f P\log P\cdot T^{-2} \ll 1$, using $P \le T$.
(d) *Contour shift.*  Put $\sigma_1 = 1 - (\log T)^{-2/3-\varepsilon}$; for $T \ge T_1(\varepsilon)$ this is
to the right of the (VKZ) boundary at height $2T$ (as $(\log 2T)^{2/3}(\log\log 2T)^{1/3}/c_0 \le (\log T)^{2/3+\varepsilon}$),
and for $3 \le T < T_1(\varepsilon)$ the lemma is trivial after enlarging $C$: then $P \le T < T_1$, so the left side is bounded in terms of $f$ and $\varepsilon$ alone.
Shift the segment $[\sigma_0 - iT, \sigma_0 + iT]$ to $[\sigma_1 - iT, \sigma_1 + iT]$.  On the closed
rectangle, $s + it$ has $|\mathrm{Im}(s+it)| \le \frac32 T \le 2T$, so (VKZ) applies; the only pole is
at $s + it = 1$, i.e. $s = 1 - it$, which lies inside since $|t| \le T/2 < T$.  Its residue is
$\tilde f(1-it)P^{1-it}$ (as $-\zeta'/\zeta$ has residue $+1$ at $1$).
(e) *Bounds.*  On the horizontal sides ($|\mathrm{Im}\,s| = T$), $|\mathrm{Im}(s+it)| \ge T/2 \ge 1$, so
$|\zeta'/\zeta(s+it)| \le C_0\log 2T + 2$; with $|\tilde f| \ll_f T^{-3}$ and $|P^s| \le eP$ these
contribute $\ll_f P T^{-3}\log T \ll 1$.  On the left side, $|P^s| = P\exp(-\log P/(\log T)^{2/3+\varepsilon})$,
$|\zeta'/\zeta(s+it)| \le C_0\log 2T + |s + it - 1|^{-1} \le C_0\log 2T + (\log T)^{2/3+\varepsilon}$, and
$\int|\tilde f(\sigma_1+iy)|dy \ll_f 1$ by (a); this contributes $\ll_{f} P\exp(-\log P/(\log T)^{2/3+\varepsilon})\log T$.
Collecting (c)–(e) gives the claim.  $\square$

Teräväinen's **Lemma 8** ($k = 1$: $|P(1+it)| \ll \exp(-(\log N)^{1/10})$ for $\exp((\log N)^{1/3}) \le |t| \le N^{A\log\log N}$)
is a numbered alternative, but it is stated for sharp dyadic sums over $n \sim N$; our $p$-range
$[(1-\frac\delta2)\sqrt Z, (1-\frac\delta4)\sqrt Z]$ is sub-dyadic and smoothly weighted, so it does
not apply verbatim.  Lemma VK is the clean input.

**(PNT) Prime number theorem with classical error.**  $\psi(y) = y + O(y\exp(-c\sqrt{\log y}))$ for an
absolute $c > 0$ (de la Vallée Poussin; e.g. Davenport, *Multiplicative Number Theory*, ch. 18).  Consequence
used: for $y \ge y_0$ and $y \exp(-4(\log y)^{1/3}) \le H \le y$,
$$\pi(y + H) - \pi(y) \ge \frac{H}{2\log(2y)},$$
since the error $O(y e^{-c\sqrt{\log y}})$ is $o(H)$ and prime powers contribute $O(\sqrt{y}\log y)$.
(Not re-opened this session; textbook.)

*Lean note (this revision).*  The PNT the repo already has is PNT+'s `MediumPNT`,
$\psi(x) - x = O(x\exp(-c(\log x)^{1/10}))$ for some $c > 0$ (checked in the pinned package; its
`StrongPNT` with $\exp(-c\sqrt{\log x})$ is still commented out there).  That error is **not** $o(H)$
for $H = y\exp(-4(\log y)^{1/3})$, so with `MediumPNT` alone Lemma 3 fails at the parameters of §2.
It is repaired by one parameter change: take $T_0 = \exp(\kappa(\log Z)^{1/10})$ with $\kappa = c/8$.
Then $H \ge y/(4T_0^3) \ge y\exp(-\frac c2(\log y)^{1/10})$ for large $Z$, which beats the `MediumPNT`
error by a factor $\exp(\frac c2(\log y)^{1/10})/\log y \to \infty$.  The rest is unchanged except that
$1/T_0$ (in Lemma 4's main term and in Proposition 6's first term) is now $\exp(-\kappa(\log Z)^{1/10})$,
so the exceptional set becomes $\ll Y\exp(-c'(\log Y)^{1/10})$ for some $c' > 0$.  This is still $o(Y)$:
Theorem A's density-zero content and Corollary B survive, with the weaker rate.

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

*Proof.*  Let $g_0(u) = g(u)/u$, smooth with support in $[1-\frac\delta2, 1-\frac\delta4]$.  Then
$$P(1+it) = \sum_n \Lambda(n)\, g\Big(\frac{n}{\sqrt Z}\Big)n^{-1-it} - \sum_{k\ge2}\sum_{p}(\log p)\,g\Big(\frac{p^k}{\sqrt Z}\Big)p^{-k(1+it)},$$
where the second sum removes the prime powers $p^k$, $k \ge 2$, in the support (this identity is exact,
since $P$ runs over primes only).  The $k \ge 2$ part has $O(Z^{1/4}\log Z)$ terms, each
$\ll \log Z/\sqrt Z$, so it is $\ll Z^{-1/4}\log^2 Z$.  For the main part,
$$\sum_n \Lambda(n) g\Big(\frac n{\sqrt Z}\Big) n^{-1-it} = \frac{1}{\sqrt Z}\sum_n \Lambda(n)\, n^{-it} g_0\Big(\frac{n}{\sqrt Z}\Big).$$
Apply Lemma VK with $f = g_0$, $P = \sqrt Z$, $T = 16Z$.  Its hypotheses hold: $P \le T$, and
$|t| \le 8X < 8Z = T/2$.  So the main part is
$$\frac{1}{\sqrt Z}\Big[\tilde g_0(1-it)\,\sqrt Z^{\,1-it} + O_{\delta,\varepsilon}\Big(\sqrt Z\exp\Big(-\frac{\log\sqrt Z}{(\log 16Z)^{2/3+\varepsilon}}\Big)\log(16Z) + 1\Big)\Big].$$
The first term has modulus $|\tilde g_0(1-it)| \ll_\delta (1+|t|)^{-1} \le T_0^{-1}$ for $|t| \ge T_0$
(Lemma VK proof, step (a), $B = 1$).  Since $\frac12\log Z/(\log 16Z)^{2/3+\varepsilon} \ge (\log Z)^{1/3-2\varepsilon}$
for large $Z$, the second is $\ll \exp(-(\log Z)^{1/3-2\varepsilon})\log Z + Z^{-1/2}$.  All
contributions are $\ll \eta_Z$ after renaming $\varepsilon$ (note $T_0^{-1} = \exp(-(\log Z)^{1/3}) \le \eta_Z$).  $\square$

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
3. For $X/(2h_1) \le T \le 4X$: $\frac{X}{h_1T}\int_T^{2T}|A|^2 \le \frac{X}{h_1 T}\cdot\frac{\eta_Z^2}{\log^2 Z}\cdot\frac{2T + O(\sqrt Z)}{\sqrt Z\log Z} \ll \eta_Z^2\delta^{-1}(\log Z)^{-3}$
   (Lemmas 4, 5; $[T, 2T] \subset [T_0, 8X]$ since $X/(2h_1) \ge T_0$, and $\frac{X}{h_1T} \le 2$).  For $T > 4X$: by (MVT) applied to $A$ itself (length $\le 2X$),
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
$N_k \le Y < N_{k+1}$: $\#(\mathcal E \cap [1, Y]) \le \sum_{j < k}\#(E_j\cap[1, N_{j+1}]) + \#(E_k \cap [1,Y])$.
Note $E_j \subset E_{j+1}$ (a smaller margin is easier to miss).  Choose $N_5 < N_6 < \cdots$ inductively
with $\#(E_k \cap [1, Y]) \le Y/k^2$ for all $Y \ge N_k$ (possible since $E_k$ has density $0$); this
condition involves only $N_k$, so there is no circularity.  Then
$\sum_{j<k}\#(E_j\cap[1,N_{j+1}]) \le (k-5)\,\#(E_{k-1}\cap[1,N_k]) \le (k-5)N_k/(k-1)^2 \le Y/k$ for $k$ large,
and $\#(E_k\cap[1,Y]) \le Y/k^2$, so $\#(\mathcal E \cap [1,Y]) \le 2Y/k \to 0$.
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

1. **(VK) input.**  *Superseded in draft 2:* the displayed step from MR16's proof of Lemma 11 is replaced
   by Lemma VK (§1), stated with hypotheses ($P \le T$, $|t| \le T/2$, standard Mellin) and proved
   inline from the textbook region (VKZ).  What is genuinely needed (corrected per independent referee
   issue 5): term 2 of §6 divided by $\mu_Z^2$ is $\asymp \sup|P|^2\log Z/\delta^3$, so density zero
   needs only $\sup_{T_0\le|t|\le X/h_1}|P(1+it)| = o((\log Z)^{-1/2})$.  The classical
   de la Vallée Poussin region gives **no** saving here, because $\log T \asymp \log P$ makes
   $\exp(-c\log P/\log T)$ a constant; a region of width $(\log T)^{-1+\kappa}$ for some $\kappa > 0$, such
   as VK, is what produces the $o(1)$.
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
6. **Measure vs integers in Chebyshev.**  $\mathcal V_Z$ is a union of intervals (as $S_1$ is a step function
   of $x$), so it is measurable; fine.
7. **Is the $(1-\delta)$ constant right?**  Lemma 1 gives margin $(1-\frac{3\delta}4)\sqrt Z \ge (1-\delta)\sqrt n$
   on the range.  The witness factor $p \ge (1-\frac\delta2)\sqrt Z$ while the window is $\frac\delta4\sqrt Z$;
   both choices are inside the $\delta$ budget.  **OK.**
8. **Novelty.**  Routine for an expert in the MR/Teräväinen school (85%); not found written (LIT sweep,
   2026-10-01), and sharper than Tao's stated $n^{1/2+o(1)}$.  `papers followups` on 1510.06005 and
   2207.05038 still to run before calling it new in public.

**Overall: ~80% correct as written; the one substantive dependency to firm up is (VK) as a citable lemma.**

## 9. Revision after the independent referee (draft 2, 2026-10-01)

Every numbered issue of the independent referee (below) and where it is addressed:

| # | Issue | Resolution |
|---|---|---|
| 1 | MR16's contour line $1 - c(\log T)^{-2/3+\varepsilon}$ is a typo (outside the VK region) | No longer quoted.  §1 now states (VKZ) from the textbook and proves **Lemma VK** inline with $\sigma_1 = 1 - (\log T)^{-2/3-\varepsilon}$, inside the region. |
| 2 | Mellin convention: MR's main term $\tilde f(1+it)P^{1+it}/(1+it)$ is wrong under the standard transform | Lemma VK uses the standard $\tilde f(s) = \int f(x)x^{s-1}dx$ and main term $\tilde f(1-it)P^{1-it}$, no $1/(1-it)$.  The paper only used decay in $|t|$, which holds either way. |
| 3 | DOOR Prop 3 lacked $P \le T$ (false at $T = 2$) | Lemma VK assumes $P \le T$, used in step (c).  DOOR's corrected Prop 3 is now the textbook region (VKZ), and Lemma VK is a wiring node, not a literature Prop (see DOOR §"E3 literature Props"). |
| 4 | DOOR Prop 1 false for complex $a_n$ with one-sided integrals | (PAR′) notes the real-coefficient restriction; DOOR's corrected Prop 1 integrates over $|t|$ for complex $a_m$, with the counterexample as control 1a. |
| 5 | §8 item 1 overstated what is needed | Rewritten (§8 item 1). |
| 6 | MR's proof gives the tail $\max_{T \ge X/(2h_j)}$; MVT constant $T$ vs $2T$ | (PAR′) now uses $X/(2h_1)$; Proposition 6 term 3 starts at $X/(2h_1) \ge T_0$; MVT stated with an absolute $C$. |
| 7 | Corollary B's choice of $N_{k+1}$ self-referential | Rewritten with the single condition $\#(E_k\cap[1,Y]) \le Y/k^2$ for $Y \ge N_k$ and $E_j \subset E_{j+1}$. |
| 8 | Cosmetic (§8 numbering, unused hypothesis, sharper rate) | Numbering fixed.  The sharper rate $Y\exp(-c(\log Y)^{1/3}(\log\log Y)^{-1/3})$ is available but not pursued. |

**Related work** (added per referee "Novelty"; abstract opened 2026-10-01).  Xu Zhang, *On the sum of
least prime factors in short intervals*, arXiv:2608.24930 (2026-08-22): for composites $n$ in
$[x, x + Cx^{1/2}(\log x)^2]$, the window sums $\mu_C(x) = \sum p(n)/n$ have mean $4C$ and variance
$O_C((\log X)^{-2})$, so $\mu_C(x) = 4C + o(1)$ for almost all $x$ (an Erdős–Graham question);
uniformity is shown under a Cramér-type hypothesis.  Its windows are longer by $(\log x)^2$ and it
does not localise $p(n)$ near $\sqrt x$, so it neither implies nor is implied by Theorem A, but it is
the nearest published neighbour and should be cited.

**Self-referee of the changed parts.**
- *Lemma VK, step (c):* tail bound $\int_{|y|>T}|\tilde f(\sigma_0+iy)|\,eP\log P\,dy \ll_f P\log P\,T^{-2}$
  with $B = 3$; with $P \le T$ this is $\ll \log P/P \ll 1$.  ✓.
- *Step (d):* pole location $s = 1-it$ has $|\mathrm{Im}\,s| = |t| \le T/2 < T$, inside the rectangle;
  on the rectangle $|\mathrm{Im}(s+it)| \le T + T/2 \le 2T$, within (VKZ) at height $2T$.  ✓.  The
  small-$T$ range $T < T_1(\varepsilon)$ is absorbed into $C$ because $P \le T$ then bounds $P$, hence the
  whole left side (this is the second use of $P \le T$; without it, bounded $T$ and huge $P$ would
  claim a power saving in the smoothed PNT, which is false).  ✓.
- *Step (e):* the left-side bound needs $|s+it-1| \ge 1 - \sigma_1 = (\log T)^{-2/3-\varepsilon}$, true on
  $\mathrm{Re}\,s = \sigma_1$.  ✓.
- *Lemma 4 application:* $T = 16Z \ge \sqrt Z = P$; $|t| \le 8X = 8(1-\frac\delta2)Z < 8Z$.  The
  conversion $\frac12\log Z/(\log 16Z)^{2/3+\varepsilon} \ge (\log Z)^{1/3-2\varepsilon}$ holds for large $Z$.  ✓.
- *Proposition 6 term 3 from $X/(2h_1)$:* $X/(2h_1) \ge X/h \asymp \sqrt Z/\delta \ge T_0$, and for
  $T \in [X/(2h_1), X/h_1]$ the factor $X/(h_1T) \le 2$, so the bound is as before.  ✓.
- *MediumPNT variant:* $T_0 = \exp(\kappa(\log Z)^{1/10})$ still satisfies $T_0 \le X/(2h_1)$, $h_2 = X/T_0^3 \ge h_1$,
  and $1/T_0 \le$ the new rate; Lemma 4's first term is $\le 1/T_0$.  ✓.
- *Unchanged risk:* (VKZ) and (PNT) theorem numbers not re-opened (textbook facts; 80% on the numbers,
  ~99% on the statements).

**Overall after revision: ~90%** that Theorem A and Corollary B are correct as written; the residual
risk is in un-reopened textbook citations, not in the argument.

## Independent referee (2026-10-01)

Hostile referee pass by a separate agent.  Sources opened this pass: MR16 (arXiv:1501.04585) and
Teräväinen (arXiv:1510.06005), full text via `pdftotext`; Tao's 2024-08-19 post with the LaTeX alt
text of his 19 Aug 7:55 pm reply; erdosproblems.com/385 (fetched 2026-10-01).  Every step of §§2-7 was
re-derived by hand.  IK, Ivić and Titchmarsh were not opened.

**Verdict: minor gaps.**  The argument is correct; the issues below are citation hygiene, one
convention ambiguity, and two literature Props in the DOOR file's E3 freeze list that are false as
written (they do not affect the paper proof, which states them correctly, but they would make a Lean
headline vacuous).

### What was checked and holds

- **Reduction (Lemmas 1-2).**  $a_m > 0$ forces $m = pq$ with $(1-\frac\delta2)\sqrt Z \le p \le (1-\frac\delta4)\sqrt Z < \sqrt Z \le q$, so $p < q$, $m$ composite, $p(m) = p$, and the representation is unique.  Margin $(1-\frac{3\delta}4)\sqrt Z \ge (1-\delta)(1+\frac\delta4)\sqrt Z \ge (1-\delta)\sqrt n$ on $n \le (1+\frac\delta2)Z$.  $h_1 = \lfloor h/2\rfloor - 1$ gives $[x, x+h_1] \subset [n-h, n-1]$ for $x \le n - h/2$.  The overlap count $(h/2+1)$ is right.  $\mathcal V_Z \subset [Z, (1+\frac\delta2)Z] \subset [X, 2X]$ needs $\delta \le 2/3$; fine.
- **Support / size.**  $(1-\frac\delta4)(1+2\delta) \le 1 + \frac{7\delta}4 < 2 - \delta$ iff $\delta < 4/11$.  $a_m \le \frac12$.  Factorisation $A = PQ/\log Z$ is exact.
- **Lemma 3.**  $(1+\frac\delta2)/(1-\frac\delta2) = 1 + \delta/(1-\frac\delta2) \le 1 + \frac{8\delta}7$ (equality at $\delta = 1/4$), so the $q$-constraint is automatic.  $H/y \ge (1-\frac\delta2)/(2T_0^3) \ge 1/(4T_0^3)$, and $4T_0^3 \le \exp(4(\log y)^{1/3})$ since $4\cdot 2^{-1/3} > 3$.  de la Vallée Poussin suffices.  Mertens with $o(1)$ error needs PNT (stated).  $\log\frac{1-5\delta/16}{1-7\delta/16} \ge \frac{\delta/8}{1-5\delta/16} \ge \frac\delta8$.  So $c_1 \approx 1/16$.
- **(PAR′) against the sources.**  MR16 Lemma 14 and Teräväinen Lemma 1 quotes are accurate (including Teräväinen's double $1/h$ normalisation typo and the omitted $|a_n| \le 1$).  In MR's proof the parameters enter only through $\frac1{h_1}U_1 - \frac1{h_2}U_2 \ll T_0^2 x h_2/X^2$, which uses $|A(1+it)| \le \sum|a_m|/m \ll 1$; with $h_2 \le X/T_0^3$ this is $\ll 1/T_0$.  Confirmed.  Support in $[X,2X)$ means $A$ captures every $m$ that any $S_j(x)$, $x \le 2X$, can see.
- **Lemmas 4-5, Proposition 6.**  Ranges check: $X/h_1 \le 16\sqrt Z/\delta \le 8X \le T/2$ with $T = 16Z$, so the residue at $s = 1+it$ is inside the truncated contour.  VK error at $P = \sqrt Z$, $\log T \asymp 2\log P$ is $\exp(-c(\log Z)^{1/3-\varepsilon})$ (the file's $\frac13$ in place of $\frac12$ is conservative).  Prime-power removal $\ll Z^{-1/4}\log^2 Z$.  MVT on $Q$: $(U + 2\sqrt Z)\sum q^{-2} \ll (U+\sqrt Z)/(\sqrt Z\log Z)$.  Term 2 $\ll \eta_Z^2/(\delta\log^3 Z)$; term 3 split at $4X$ correct; the $T > 4X$ tail is $\ll 1/h_1$.
- **Chebyshev and covering.**  $\mathrm{meas}(\mathcal V_Z)\mu_Z^2 \le X\mathcal D$; $Z_{j+1} + h(Z_{j+1}) \le (1+\frac\delta2)Z_j$ for large $Z_j$; the $\sqrt Y$ split and $\varepsilon$-renaming are fine.
- **Upper bound.**  $m + \sqrt m$ is increasing, so $F(n) \le n - 1 + \sqrt{n-1} < n + \sqrt n$.

### Issues

1. **(VK) display: MR's contour exponent is a typo, quoted verbatim.  Severity: minor (citation).**
   MR16 p. 17-18 says "shift the contour to $\sigma = 1 - c(\log T)^{-2/3+\varepsilon}$".  Since $(\log T)^{-2/3+\varepsilon}$ exceeds the VK width $(\log T)^{-2/3}(\log\log T)^{-1/3}$, that line lies *outside* the zero-free region.  Their next sentence ("zeros ... are $\gg (\log T)^{-2/3+\varepsilon}$ away", the bound $\zeta'/\zeta \ll (\log T)^{1+2/3+\varepsilon}$) and the final error $P\exp(-\log P/(\log T)^{2/3+\varepsilon})$ are consistent only with $\sigma = 1 - c(\log T)^{-2/3-\varepsilon}$.  The derivation is right; the quoted line is not.
   *Fix:* do not quote the contour line; state Lemma 4's input as a numbered lemma of your own with hypotheses ($f$ smooth, compactly supported in $(0,\infty)$; $2 \le P \le T$; $|t| \le T/2$) and give the 10-line Mellin + zero-free-region proof, citing the VK zero-free region from a textbook (theorem number to be verified, not checked here).  Teräväinen's **Lemma 8** ($k = 1$, verified this pass: $|P(1+it)| \ll \exp(-(\log N)^{1/10})$ for $\exp((\log N)^{1/3}) \le |t| \le N^{A\log\log N}$) is a numbered alternative, but it is stated for sharp dyadic $n \sim N$, and the $p$-range here is sub-dyadic, so it does not apply verbatim either.

2. **Mellin convention in (VK).  Severity: minor for the paper, major for the Lean Prop.**
   MR's (15) carries $P^s/s$, so their main term is $\tilde f(1+it)P^{1+it}/(1+it)$.  With the standard Mellin transform $\tilde f(s) = \int_0^\infty f(x)x^{s-1}dx$ the residue is $\tilde f(1+it)P^{1+it}$ with **no** $1/(1+it)$.  The paper only uses the decay of the main term in $|t|$, so either reading works.  But DOOR's E3 Prop 3 (`Literature.VKSmoothPrimeSum`) writes the $/(1+it)$ form without pinning $\tilde f$: under the standard convention it is off by $\asymp P|t|$ for $|t| \asymp 1$, hence false.
   *Fix:* pin $\tilde f$ in the Prop, or (better) freeze Lemma 4's conclusion itself as the Prop.

3. **DOOR Prop 3 has no $P \le T$ hypothesis, so it is false.  Severity: major for the Lean plan (paper unaffected).**
   As written ("all $T \ge 2$, $P \ge 2$, $|t| \le T$"), take $T = 2$, $t = 0$: the error bound is $C P\exp(-\log P/(\log 2)^{2/3+\varepsilon}) = C P^{1-1/(\log 2)^{2/3+\varepsilon}} = o(1)$, a saving beyond $P^{-1/4}$, contradicting the $\Omega(P^{1/2})$ oscillation of the smoothed explicit formula.  In MR's derivation $T$ is the truncation height and the truncation error is $O_B(P^2 T^{-B})$, so $T \ge P^{c}$ is implicit.  Our use has $T = 16P^2$.
   *Fix:* add $P \le T$ (or freeze Lemma 4 directly with $P = \sqrt Z$, $T_0 \le |t| \le 8X$).

4. **DOOR Prop 1 (Teräväinen Lemma 1 "verbatim" + $|a_n| \le 1$) is false for complex $a_n$.  Severity: major for the Lean plan; (PAR′) in §1 is stated correctly.**
   Teräväinen allows complex $a_n$ but integrates only $t \in [T_0, X/h_1]$.  Counterexample: $a_m = m^{-i\tau}$ on $[X, 2X)$ with $\tau = X/(10h_1)$ and $h_1 \le X/(10T_0^3)$.  Then $|S_1/h_1| \ge 0.9 - o(1)$, $|S_2/h_2| \ll T_0^3/\tau \to 0$, so LHS $\asymp 1$, while $|A(1+it)| \ll 1/|t + \tau| + o(1)$ is small for all $t > 0$, making the RHS $\to 0$.  MR's proof only covers $t > 0$ via $A(1-it) = \overline{A(1+it)}$, i.e. real coefficients.
   *Fix:* require real $a_n$ (our case), or integrate over $T_0 \le |t| \le X/h_1$ and $T \le |t| \le 2T$.

5. **§8 item 1 overstates what is needed.  Severity: trivial.**
   The ratio $\mathrm{term\,2}/\mu_Z^2 \asymp \sup|P|^2\log Z/\delta^3$, so Corollary B (density zero) needs only $\sup_{T_0\le|t|\le X/h_1}|P(1+it)| = o((\log Z)^{-1/2})$, not a saving "beating $\log^4 Z$".  The de la Vallée Poussin parenthetical is muddled: with $\log T \asymp \log P$ the classical region gives *no* saving at all, which is the real reason VK is needed.  Conclusion unchanged.

6. **MR16 Lemma 14's tail range.  Severity: trivial.**  MR's proof (eq. (19)) actually gives $\max_{T \ge X/(2h_j)}$, not $T \ge X/h_1$.  Lemma 4 covers $T \ge X/(2h_1) \ge T_0$ anyway, so add one clause.  Similarly MR's Lemma 6 is printed with $T + O(N)$ where Montgomery–Vaughan has $2T + O(N)$; harmless.

7. **Corollary B's choice of $N_{k+1}$ is self-referential.  Severity: trivial.**  "$\sum_{j \le k}\#(E_j\cap[1,N_{j+1}]) \le N_{k+1}/k$" has $N_{k+1}$ on both sides.  It is satisfiable (earlier terms fixed, $\#(E_k \cap [1,N]) = o(N)$); say so, and note $E_j \subset E_{j+1}$.

8. **Cosmetic.**  §8 numbering skips 6.  Lemma 1's hypothesis $n \ge Z+h$ is used only in Lemma 2.  The sharper exceptional set $Y\exp(-c(\log Y)^{1/3}(\log\log Y)^{-1/3})$ is available from the same input if wanted.

### Sanity: does any step prove something open?

No.  The saving comes from one VK-small factor $P$ of length $\sqrt Z$ times the MVT on a second factor $Q$ whose length $\sqrt Z$ matches $X/h_1 \asymp \sqrt Z/\delta$, so the MVT costs only $O(1/\delta)$.  That regime is classical; it collapses at $h = Z^{1/2-\kappa}$ (§7a item 2) and gives nothing for primes alone (§7a item 1).  Known neighbours do not imply Theorem A: Huxley ($\theta > 1/6$) and Guth–Maynard ($\theta > 2/15$) are about primes; Harman's $E_2$ in $[x, x+\log^{7+\varepsilon}x]$, Teräväinen's $E_2$ in $[x, x+\log^{3.51}x]$ (verified in 1510.06005 Theorem 3) and its sequel 2207.05038 all use one tiny factor ($P_1 = (\log X)^{2.51}$ in Teräväinen Theorem 5), so they say nothing about $p(m) \ge (1-\delta)\sqrt m$.  Tao's reply (verified verbatim via alt text) predicts exactly this territory: "for $\theta$ slightly below $1/2$, almost all such intervals $[n - n^\theta, n]$ should contain semiprimes whose prime factors are at least $n^\theta$ ... and in fact should give the asymptotic $f(n) = n + n^{1/2+o(1)}$ for almost all $n$".  Theorem A is the $\theta = 1/2$, constant-$\delta$ endpoint of that remark.

### Novelty

Not found by these instruments (a miss is not absence):
- `papers followups 1510.06005` (18 citing), `1501.04585` (183 listed, well below MR16's true citation count, so incomplete), `2207.05038` (6 citing).  No title concerns balanced semiprimes, Erdős #385, or $F(n)$.
- arXiv API abstract searches ("least prime factor" + "short intervals", semiprimes, rough numbers, Erdős 385).  Weak instrument: a phrase search for "almost all short intervals" returned 7 hits and missed known titles.
- erdosproblems.com/385 (2026-10-01): OPEN, 2 comments, 0 proof claims, no almost-all result recorded.
- **Nearest neighbour:** Xu Zhang, *On the sum of least prime factors in short intervals*, arXiv:2608.24930 (2026-08-22, single author, unrefereed): $\sum_{x\le n\le x+C\sqrt x\log^2 x,\ n\ \text{comp.}} p(n)/n = 4C + o(1)$ for almost all $x$ (Erdős–Graham question).  Windows are longer by $\log^2 x$ and $p(n)$ is not localised near $\sqrt x$, so it does not imply Theorem A; cite it as related work.

Agree with §8 item 9: routine for the MR/Teräväinen school (~85%), apparently unwritten.

### Overall

Theorem A and Corollary B are correct as argued: **~90%** (residual risk is in un-reopened textbook inputs, not in the bookkeeping).  Before freezing E3 in Lean, fix DOOR Props 1 and 3 (issues 3-4) and pin the Mellin convention (issue 2); a false literature Prop would make the headline vacuous.
