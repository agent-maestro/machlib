# MathOverflow post — ready to paste

Paste the **Body** below into the MO editor as-is (it is MathJax, not Lean). Fill the one `<LINK>`
placeholder first. Everything above the horizontal rule is instructions to the poster and is not
part of the question.

**Title**

> Is asymptotic separation of exp–log germs uniform in the defining complexity?

**Tags** (five is MO's maximum; the first is the arXiv-style top-level tag MO expects on an analysis
question)

> `ca.classical-analysis-and-odes` `o-minimality` `asymptotics` `hardy-fields` `model-theory`

If the tag picker does not offer `hardy-fields`, use `differential-algebra`; if it does not offer
`asymptotics`, use `real-analysis`. Do not invent a `transseries` tag — mention transseries in the
body instead, which is already done.

**Link to fill.** `<LINK>` → the long version in the repo:
`https://github.com/agent-maestro/machlib/blob/master/exploration/germ_approach_problem_statement_2026_09_23.md`
(this branch must be pushed to `master` before posting, or the link 404s).

---

## Body

**The class.** An *expression* is built from a constant symbol for each real $c$, the variable $x$,
and one binary constructor $\langle A,B\rangle$. Each expression $t$ denotes a function
$[\![t]\!]$ on the reals by

$$[\![c]\!](x)=c,\qquad [\![x]\!](x)=x,\qquad
[\![\langle A,B\rangle]\!](x)=\exp\bigl([\![A]\!](x)\bigr)-L\bigl([\![B]\!](x)\bigr),$$

where $L$ is the **totalised** logarithm: $L(y)=\log y$ for $y>0$ and $L(y)=0$ for $y\le 0$. The
*depth* is the usual one: $d(c)=d(x)=0$ and $d(\langle A,B\rangle)=1+\max\bigl(d(A),d(B)\bigr)$.

One constructor edge buys one exponential — $\langle A,0\rangle$ and $\langle A,1\rangle$ both
denote $\exp\circ[\![A]\!]$ — and also one logarithm, since $\langle 0,B\rangle$ denotes
$1-L([\![B]\!])$. Composing, $\langle\langle 0,B\rangle,1\rangle$ denotes $e/[\![B]\!]$ wherever
$[\![B]\!]>0$: **a reciprocal costs two edges**, which matters below. Writing $T_0(x)=x$ and
$T_{k+1}=\exp\circ T_k$, the tower $T_k$ is denoted at depth exactly $k$.

Every $[\![t]\!]$ agrees near $+\infty$ with a function in Hardy's class $\mathcal L$ of
logarithmico-exponential functions: $L$ is first-order definable in $\mathbb R_{\exp}$, and an
$\mathcal L$-germ has eventually constant sign, so past some point $L([\![B]\!])$ is either
$\log[\![B]\!]$ throughout or $0$ throughout.

**Conjecture.** *For every $j\in\mathbb N$ there exists $k\in\mathbb N$ with the following
property. Let $A,C$ be expressions with $d(A)\le j$ and $d(C)\le j$, let $X_0\ge 1$, and suppose
$[\![C]\!](x)<\exp([\![A]\!](x))$ for all $x\ge X_0$. Then there is $X_1\ge X_0$ with*

$$\exp\bigl(-T_k(x)\bigr)\ \le\ \exp\bigl([\![A]\!](x)\bigr)-[\![C]\!](x)
\qquad\text{for all } x\ge X_1 .$$

**The quantifier position is the entire content.** Read it as $\forall j\,\exists k\,\forall(A,C)$.
With the quantifiers exchanged — $k$ chosen after the pair — it is classical, in three lines: the
gap germ lies in $\mathcal L$ and is not the zero germ; $\mathcal L$ is a field, so the gap's
reciprocal lies in $\mathcal L$; every $\mathcal L$-germ is $o(\exp^{\circ k})$ for some $k$; apply
that to the reciprocal and use $1/u\ge e^{-u}$ for $u\ge1$. (That last step is a fact about
$\mathcal L$ specifically, *not* about Hardy fields in general, which may be transexponential.) So
I am not asking whether these germs can be separated — pairwise they can, since 1912 — but whether
the **rate** of separation is bounded in terms of the defining complexity alone.

Two misreadings worth heading off: it is not "bounded away from zero" ($\exp(1-x)$ and $e/x$ have
infimum $0$ and both satisfy the conjecture at $k=0$), and the strict hypothesis cannot be dropped
($\langle A,1\rangle$ denotes $\exp\circ[\![A]\!]$ on the nose, so the gap can be identically zero).

**What is known.** An equivalent one-expression form — for every $j$ there is $k$ such that every
$t$ with $d(t)\le j$ whose germ is positive on a ray satisfies $\exp(-T_k(x))\le[\![t]\!](x)$
eventually — is proved at depth $\le 2$ with $k=0$ and at depth $3$ with $k=2$. For a lower bound:
the expression denoting $\exp(1-T_{m+1}(x))$ has depth exactly $m+4$, is positive, and lies
strictly below $\exp(-T_m(x))$ at every $x\ge1$; so $k\ge j-3$ at depth $j$, and no single $k$
serves all depths. Sweeps exhaustive at depths $2$ and $3$ and a beam search to depth $7$ produced
no counterexample; the required height reads $j-3$ under a metric absorbing an additive constant in
the exponent, and $j-2$ for the envelope exactly as displayed. Every search ranges over a finite
constant alphabet while the grammar allows an arbitrary real at every leaf, so this is
failure-to-contradict, not evidence.

**Eight descent mechanisms are ruled out**, each by a machine-checked theorem, which is why I am
asking rather than inducting:

1. any $\mathbb N$-valued measure on expressions descending strictly into both children — the
   reciprocal costs two edges while an induction step buys one;
2. any measure read off the germ's growth rate — totalisation makes $\langle 0,T_{n+1}\rangle$
   eventually negative while its right child is the $(n{+}1)$-fold tower, so growth does not
   descend to the right, and unboundedly so;
3. peeling one exponential — $C\cdot(A-\log C)\le\exp A-C$ is in the right direction, but
   $A-\log C$ sits one level *above* $A$ and $C$;
4. any measure into any well-founded order, descending into both children (proved from
   well-foundedness alone: lexicographic orders, vectors, ordinal ranks, polarity-indexed variants);
5. any parameter factoring through the germ — this class is *empty*, not merely inadequate: four
   constructor edges return the value to $[\![t]\!]$ at every real point, closing a cycle; the
   one-sided and guarded variants die too;
6. a one-sided syntactic recursion whose step is the peel of (3) — it terminates in at most $j$
   steps, but each of its two terminal cells is provably *equivalent* to the conjecture;
7. enlarging the class of right-hand germs — it is already closed under $+,-,\times,\exp,L$, and
   for any class the terminal cell quantifies over the class and so grows with it;
8. any well-founded relation on pairs $(A,C)$ that the peel decreases — its minimal elements are
   (6)'s cell.

The nearest things I have found both miss. Berarducci–Servi's effective o-minimality for
$\mathbb R_{\exp}$ bounds component counts computably in formula complexity: the right kind of
syntactic uniformity, the wrong quantity, since a count cannot produce a floor ($e^{-x}$ has no
zeros and infimum $0$). Łojasiewicz-type separation is polynomially shaped, and that shape does not
extend to o-minimal expansions defining $\exp$ — which is why the envelope here is tower-scale.
Transseries has the right vocabulary *for a transmonomial*; differences break the correspondence,
and that break is precisely this conjecture.

**Question.** Is there a complexity-dependent class of transmonomials $\mathcal M_j$ such that
whenever $f\ne g$ are germs denoted by expressions of depth $\le j$, one eventually has
$|f(x)-g(x)|\ge c\,m(x)$ for some $c>0$ and some $m\in\mathcal M_j$? Equivalently: **does bounded
defining complexity uniformly bound the asymptotic complexity of the leading surviving term after
arbitrary cancellation?**

This arose in a Lean formalisation, where it is one open obligation; nothing practical depends on
the answer, and the result it was meant to unlock does not provably follow from it, so a refutation
would be worth as much to me as a proof — and a pointer to a formulation I have failed to recognise
worth more than either. Long version, with the machine-checked statements and the searches: <LINK>.
