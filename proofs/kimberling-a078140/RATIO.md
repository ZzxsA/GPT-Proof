# The ratio limit and the optimal growth factor

**ZzxsA and ChatGPT (OpenAI)**

For $3/2\le r<5/3$, write
$$
G(x)=\sum_{j\ge0}(-1)^j\lfloor(j+1)r\rfloor x^j,\qquad
A(x)=1/G(x)=\sum_{n\ge0} a_nx^n .
$$
Then $3a_{n+1}\ge5a_n$ for every $n\ge0$, with equality exactly at $n=1$. Thus $5/3$ is the optimal universal lower bound on consecutive ratios. There is a unique zero $\rho$ of $G$ in $|x|\le3/5$. It is real, positive and simple, and
$$
 L(r)=\lim_{n\to\infty}a_{n+1}/a_n=1/\rho,\qquad 5/3<L(r)\le2.
$$
This is an analytic proof with an exact rational certificate. The Lean files in this project establish strict increase and its parameter interval. [Kimberling's question](https://mathoverflow.net/questions/259821/another-question-about-the-golden-ratio-and-other-numbers) · [OEIS A078140](https://oeis.org/A078140)

## A direct proof of convergence

One can prove convergence on the full interval without subdividing the parameters. Use the comparison series $D^*$ and $E=D^*-(1+x)G$ from the [strict-increase proof](README.md), and put $H=1/D^*$. We have
$
 H(x)=\frac{1+x/(1-x-x^2)}{1-x-x^3}.
$
Its coefficients are positive; it is analytic on $|x|<s=(\sqrt5-1)/2$ and tends to infinity as $x$ increases to $s$. Indeed the second denominator is positive through $s$, since $1-s-s^3=s^2(1-s)>0$. The coefficients of $E$ are nonnegative and bounded. When $r<8/5$ the degree-four coefficient of $E$ is 1, and when $r\ge8/5$ its degree-nine coefficient is 1. These follow by evaluating the pairs of floors at $4r,5r$ and $9r,10r$, respectively.

It follows that $F=EH$ has zero constant term and positive coefficients in every degree from its first nonzero coefficient onward. On $[0,s)$ it increases strictly from zero to infinity. Let $R$ be the unique positive solution to $F(R)=1$. Inside $|z|<R$, $|F(z)|<1$. On the boundary, $F(z)=1$ forces equality in the triangle inequality for the absolutely convergent sum, so all nonzero summands have positive real phase. Consecutive positive coefficients then force $z=R$. Also $F'(R)>0$.

Now $A=(1+z)H/(1-F)$ has a simple pole at $R$ and no other singularity of that modulus. Since zeros of $1-F$ are isolated, some larger closed disk of radius $T<s$ contains just that zero. Subtracting $C/(1-z/R)$, where $C=(1+R)H(R)/(R F'(R))>0$, leaves an analytic function on a neighborhood of that disk. Cauchy's bound yields $a_n=C R^{-n}+O(T^{-n})$, hence the ratio tends to $1/R$. The finite certificate below gives the additional sharp inequality for each consecutive pair. [Flajolet and Sedgewick, *Analytic Combinatorics*, Ch. V](https://ac.cs.princeton.edu/home/AC.pdf)

## A certificate for all real parameters in the interval

Set $R=3/5$, $f_j=\lfloor(j+1)r\rfloor$, and $f_{-1}=f_{-2}=0$. The coefficients of $D=(1+x)^2G$ are
$$
 d_j=(-1)^j(f_j-2f_{j-1}+f_{j-2}).
$$
Here $d_0=1,d_1=-1$, and $|d_j|\le1$ for $j\ge2$, since consecutive increments of $f_j$ belong to $\{1,2\}$. These bounds give absolute convergence in the open unit disk.

The first sixteen values $d_0,\ldots,d_{15}$ are constant on each half-open interval between successive reduced fractions with denominator at most 16 in the parameter range. The thirteen left endpoints in order are
$$
3/2,\ 23/15,\ 20/13,\ 17/11,\ 14/9,\ 25/16,\ 11/7,\ 19/12,\ 8/5,\
21/13,\ 13/8,\ 18/11,\ 23/14 .
$$
For each of these prefixes, let $u_j=[x^j]\,1/D(x)$, $u_{-1}=0$, and define
$$
 c=u_{10}/u_9,\qquad Q(x)=\sum_{i=0}^{9}q_ix^i,\qquad q_i=u_i-cu_{i-1}.
$$
Writing $E=DQ=\sum e_jx^j$ gives $e_0=1,e_1=-c$, and $e_2=\cdots=e_{10}=0$. For $j>15$, the convolution bound is $|e_j|\le\sum_{i=0}^9|q_i|$. The script computes $u_j$ by triangular inversion and verifies for all thirteen prefixes that
$$
 cR-1-\sum_{j=2}^{15}|e_j|R^j
      -\Big(\sum_i|q_i|\Big)\frac{R^{16}}{1-R}>0,\qquad
 \sum_{j=0}^{15}d_jR^j+\frac{R^{16}}{1-R}<0.
$$
The least margin in the first inequality is $59553019063/6347656250000$, on the cell beginning at $21/13$. The same computation gives $3a_{j+1}\ge5a_j$ for $0\le j\le10$, with equality only for $j=1$. Each initial $a_j$ is $u_j+2u_{j-1}+u_{j-2}$, with missing values interpreted as zero.

## Infinite conclusions

The numerator of $EA=(1+x)^2Q$ has degree at most 11. For $n\ge12$,
$$
 a_n=c a_{n-1}-\sum_{j=2}^{n}e_j a_{n-j}.
$$
If consecutive ratios through index $n-1$ are at least $1/R$, then $0<a_{n-j}\le R^{j-1}a_{n-1}$. The first certified inequality gives $a_n>a_{n-1}/R$. Induction proves the bound for every index. The initial pair $a_1=3,\ a_2=5$ realizes equality.

On $|x|=R$, the same inequality gives $|E(x)+cx|<|cx|$. Rouché's theorem therefore gives exactly one zero of $E$ in the open disk, counted with multiplicity, and none on its boundary. The second inequality gives $D(R)<0$, whereas $D(0)=1$. Thus $D$ itself has a real zero $\rho\in(0,R)$. Since $E=DQ$, this zero is simple and is the only zero of $G$ on the closed disk. Subtract the principal part from $A$ at $\rho$. The remainder is analytic on a neighborhood of the closed disk, so Cauchy's coefficient bound gives
$$
 a_n=C\rho^{-n}+O(R^{-n}),\qquad C=-1/(\rho G'(\rho))\ne0.
$$
This proves $L(r)=1/\rho>5/3$. To obtain the upper bound, the coefficients of $(1+x)G_r(x)$ dominate those at $r=3/2$, namely the coefficients of $(1-2x)/(1-x^2)$. This comparison uses even unsigned increments at least 1 and odd unsigned increments at most 2. It gives $\rho\ge1/2$. For $r>3/2$, equality of every increment with the sequence at $3/2$ would force $r=3/2$ by taking long-run averages. Some coefficient comparison is therefore strict at $x=1/2$, giving $L(r)<2$. At $r=3/2$ the displayed rational function gives $L=2$.

## Arithmetic and the golden ratio

For rational $r=p/q$, $f_{j+q}=f_j+p$, so $G$ is rational over $\mathbb Q$ and $L(r)$ is algebraic. For irrational $r$, assume $L(r)$ algebraic. Apply Theorem 1 of Luca, Ouaknine and Worrell with $\theta=\alpha=r$, $\beta=-L(r)$, and the polynomial $f(t)=t$. Since $|\beta|>1$, their theorem says $\sum_{n\ge0}\lfloor nr+r\rfloor\beta^{-n}$ is transcendental. This sum equals $G(\rho)=0$, a contradiction. Thus $L(r)$ is transcendental exactly when $r$ is irrational. [Luca, Ouaknine and Worrell, *Transcendence of Hecke–Mahler series*, 2025](https://doi.org/10.1112/blms.70033)

At $\phi=(1+\sqrt5)/2$, direct integer bounds prove
$$
 1.688924110769165206686359<L(\phi)<1.688924110769165206686360.
$$
The original MathOverflow question uses $A(-x)$, giving the negative of this limit. The calculation evaluates the first 161 coefficients of $(1+x)G_\phi$ at the reciprocal endpoints, bounding the tail by $2x^{161}/(1-x)$. The coefficient comparison at $1/2$ and the uniqueness established on $|x|\le3/5$ identify the enclosed root.

Run these two standard-library scripts in this directory to reproduce the exact arithmetic.

~~~sh
python3 verify_optimal_growth.py
python3 verify_golden_limit.py
~~~
