# The maximum difference between degree and Perron-vector dispersion

## Statement

Let \(G\) be a connected, simple, undirected graph on \(n\ge2\) vertices. Choose a vertex uniformly at random. Write \(D\) for its degree and \(X\) for its entry in a positive eigenvector of the adjacency matrix belonging to the spectral radius \(\rho\). For a positive random variable \(Y\) define \(c(Y)=\operatorname{Var}(Y)/(\mathbb EY)^2\). Put \(c=c(D)\), \(e=c(X)\), \(\gamma=X_{\max}/X_{\min}\), \(\delta=D_{\min}\), \(\Delta=D_{\max}\), \(R=\Delta/\delta\), and
\[
\Gamma(G)=(c-e)/\gamma^2 .
\]

**Theorem.** Define, for \(t\ge1\),
\[
F(t)=\frac14(1-t^{-2})^2
\left[1-\left(\frac{2t}{(t+1)^2}\right)^2\right].
\]
Then
\[
\Gamma(G)\le F(\sqrt R)\le F(\sqrt{n-1})
=\Gamma(K_{1,n-1})<\frac14.
\]
Up to isomorphism, the star is the unique maximizer at every order. The supremum over all orders is \(1/4\). These assertions imply Conjecture 4.4 of Gregory J. Clark, *Linear and Multilinear Algebra* 72 (2024), 188–202. The journal version specifies the sign of \(\Gamma\) used here. [Version of record](https://doi.org/10.1080/03081087.2022.2158171)

## Coupling the two dispersions

The eigenequation and symmetry of adjacency give \(\mathbb E(DX)=\rho\,\mathbb EX\). Also, \(\rho^2\ge\mathbb E D^2\), the classical Hofmeister bound. For a direct proof, sum the following Cauchy–Schwarz inequality over all vertices \(u\),
\[
d_u^2\le\left(\sum_{v\sim u}x_v\right)
\left(\sum_{v\sim u}x_v^{-1}\right)
=\rho x_u\sum_{v\sim u}x_v^{-1}.
\]
Exchanging the two summations on the right gives \(\rho\sum_v x_v^{-1}\sum_{u\sim v}x_u=n\rho^2\). Applying Cauchy–Schwarz again, this time to the centered variables \(D-\mathbb ED\) and \(X-\mathbb EX\), yields
\[
\sqrt{1+c}\le\frac{\rho}{\mathbb ED}
=1+\frac{\operatorname{Cov}(D,X)}{\mathbb ED\,\mathbb EX}
\le1+\sqrt{ce}.
\]
If \(c>0\), subtract 1, square and divide by \(c\). If \(c=0\), use \(e\ge0\). In both cases,
\[
e\ \ge\ f(c):=\frac{c}{(1+\sqrt{1+c})^2}
=\frac{\sqrt{1+c}-1}{\sqrt{1+c}+1}.
\tag{1}
\]
In particular \(c\longrightarrow\infty\) implies \(\liminf e\ge1\). This excludes the family asked about immediately after Clark’s conjecture.

## Bounding the range

At a vertex of degree \(\Delta\), we have \(\Delta X_{\min}\le\rho X_{\max}\). At a vertex of degree \(\delta\), we have \(\rho X_{\min}\le\delta X_{\max}\). Together they give \(R\le\gamma^2\), as in Clark’s Lemma 2.3.

If \(a\le Y\le b\) with \(a>0\) and mean \(\mu\), expanding \((Y-a)(b-Y)\ge0\) gives \(\mathbb E Y^2\le(a+b)\mu-ab\). The square \(((a+b)\mu-2ab)^2\ge0\) gives
\[
c(Y)\le\frac{(b-a)^2}{4ab}.
\tag{2}
\]
If \(a<b\), equality requires \(Y\in\{a,b\}\) almost surely and \(\mu=2ab/(a+b)\). In particular \(c\le K(R):=(R-1)^2/(4R)\).

Let \(H(c)=c-f(c)=c[1-(1+\sqrt{1+c})^{-2}]\). The square-bracketed factor is positive and nondecreasing on \([0,\infty)\). Consequently \(H\) is nonnegative and strictly increasing. In order, (1), \(R\le\gamma^2\), and (2) give
\[
\Gamma(G)\le \frac{H(c)}{\gamma^2}
\le \frac{H(c)}R\le \frac{H(K(R))}R.
\tag{3}
\]
Set \(t=\sqrt R\). The identity \(\sqrt{1+K(t^2)}=(t^2+1)/(2t)\) gives \(H(K(R))/R=F(t)\).

For \(t\ge1\), the factor \((1-t^{-2})^2\) is strictly increasing. The function \(t+1/t\) is nondecreasing because its increment between \(s\) and \(t\ge s\ge1\) is \((t-s)(1-1/(st))\). Therefore \(2t/(t+1)^2=2/(2+t+1/t)\) is nonincreasing, and the second factor in \(F\) is nondecreasing and at least \(3/4\). Thus \(F\) is strictly increasing. It is less than \(1/4\) for every finite \(t\), and tends to \(1/4\) as \(t\to\infty\). Finally \(1\le R\le n-1\), since \(\delta\ge1\) and \(\Delta\le n-1\).

## Attainment and uniqueness

Let \(d=n-1\) and \(t=\sqrt d\). The star has degrees \(d,1,\ldots,1\) and a positive Perron vector \(t,1,\ldots,1\), with \(\rho=t\). Direct averaging gives \(\gamma=t\), \(c=K(d)\), and \(e=((t-1)/(t+1))^2=f(K(d))\). Every inequality in (3) is an equality. Taking \(d\to\infty\) proves that \(1/4\) is the supremum.

Suppose another graph on \(n>2\) vertices attains the same value. Strict monotonicity of \(F\) forces \(R=n-1\). Thus \(\delta=1\) and \(\Delta=n-1\). Strict monotonicity of \(H\) also forces \(c=K(R)\). Equality in (2) says every degree equals \(1\) or \(n-1\). There is a vertex of degree \(1\). It cannot be adjacent to two vertices of degree \(n-1\), so precisely one vertex has degree \(n-1\). This identifies the star. For \(n=2\) the only connected simple graph is \(K_2\).

More generally the bound at fixed \(R\) is attained by every connected bipartite graph with constant degree on each side. Indeed, for high and low degrees \(\Delta\) and \(\delta\), the two side sizes are in the ratio \(\delta:\Delta=1:R\), by counting edges. The Perron entries are constant on the two sides in the ratio \(\sqrt R:1\), as the eigenequations with \(\rho=\sqrt{\Delta\delta}\) show. These ratios reproduce exactly the two distributions in the star calculation, with \(d\) replaced by \(R\) and the degrees scaled by \(\delta\). Every rational \(R\ge1\) is realized by a complete bipartite graph.

## Uniform lower bound

Applying (2) to \(X\) gives \(e\le(\gamma-1)^2/(4\gamma)\). Hence
\[
-\Gamma(G)\le\frac{e}{\gamma^2}
\le\frac{(\gamma-1)^2}{4\gamma^3}\le\frac1{27}.
\]
The last inequality follows from \(4\gamma^3-27(\gamma-1)^2=(\gamma-3)^2(4\gamma-3)\ge0\). Together with the theorem, this answers Clark’s question about constants separating \(\Gamma\) from both \(-1\) and \(1\). This proof establishes no optimality assertion for the lower endpoint.

## Literature and scope

- Gregory J. Clark, “Comparing eigenvector and degree dispersion with the principal ratio of a graph,” *Linear and Multilinear Algebra* 72 (2024), 188–202, published online December 20, 2022. The introduction explicitly interprets the extremum at fixed order. Conjecture 4.4 and the two subsequent questions are on page 201. Preprint Conjecture 3 uses the opposite sign for \(\Gamma\), with the same denominator. [Journal version](https://doi.org/10.1080/03081087.2022.2158171) · [Oxford institutional copy](https://ora.ox.ac.uk/objects/uuid%3Ace57e3be-9b68-4934-93c4-f1a9ab477517) · [Preprint](https://arxiv.org/abs/2202.00325)
- M. Hofmeister, “Spectral radius and degree sequence,” *Mathematische Nachrichten* 139 (1988), 37–44. The first inequality in the proof above is classical. [Bibliographic record](https://doi.org/10.1002/mana.19881390105)
- P. Csikvári and V. Harangi, “The least balanced graphs and trees,” *Journal of Combinatorial Theory, Series B* 179 (2026), 147–204. This proves Clark’s separate Four’s a Crowd conjecture about the Perron-vector dispersion itself. [Journal article](https://doi.org/10.1016/j.jctb.2026.03.003)
