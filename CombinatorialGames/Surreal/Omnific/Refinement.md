# Conway’s refinement theorem for omnific integers

Take two points with whole coordinates on a line through the origin. Must they be whole
multiples of a common whole point? Let $r=\sqrt2$ and $s=\sum_{n\ge1}\omega^{1/n}$. The points
$(\omega,r\omega)$ and $(s,rs)$ are whole. In normal form, a whole number has only positive
exponents and possibly an integer constant term. Try the direction $(1,r)$.
The multipliers $\omega$ and $s$ are whole. We still have to make $r$ whole.

Multiply the row by $m=\omega^\varepsilon$ and divide both multipliers by $m$. If
$0\lt \varepsilon\lt 1/n$ for every $n\ge1$, then $m$ and $rm$ are purely infinite, and
every exponent in $\omega/m$ and $s/m$ is still positive. The simplest such exponent
is $1/\omega$. Half of it would work too. Thus

```math
\begin{pmatrix} \omega & r\omega \\ s & rs \end{pmatrix}
=
\begin{pmatrix} \omega/m \\ s/m \end{pmatrix}
\begin{pmatrix} m & rm \end{pmatrix}.
```

With real exponents and integer constant terms this same matrix has no whole
refinement. A divisor of $\omega$ in that ring is a scalar times a monomial. A positive
real exponent exceeds some $1/n$. At exponent zero we would need a nonzero integer $k$
with $rk$ an integer. This is L’Innocente and Mantova’s Example 9.1.6.
[Example 9.1.6](https://eprints.whiterose.ac.uk/id/eprint/208281/8/1-s2.0-S0001870824000288-main.pdf#page=81) ·
[The four factors from cuts](Refinement/InfinitesimalExponent.lean#L135)

A surreal $x$ is **whole**, or an **omnific integer**, if $x=\lbrace x-1\mid x+1\rbrace$.
Write $\mathbf{Oz}$ for their ring. Conway conjectured the following theorem.

**Refinement.** If $a,b,c,d\in\mathbf{Oz}$ and $ab=cd$, there are $e,f,g,h\in\mathbf{Oz}$ with

```math
\begin{pmatrix} a & c \\ d & b \end{pmatrix}
=
\begin{pmatrix} e \\ h \end{pmatrix}
\begin{pmatrix} f & g \end{pmatrix}.
```

For $a\ne0$ the two given points lie on $y=(c/a)x$. If $a=0$, either the first row or
the first column vanishes, and the other row or column gives a refinement at once.

On the same page Conway proves division with remainder by rounding a quotient. He also
points out that omnific integers admit infinite descending chains. Here rounding will
give an *exact* quotient once we find the right row. The induction that gives the theorem
is on the growth classes occurring in $a$.
[*On Numbers and Games*, chapter 5, Theorem 34 and the conjecture, p. 46](https://kyl.neocities.org/books/%5BTEC%20CON%5D%20on%20numbers%20and%20games.pdf#page=57)

## Exact division above a growth class

For a convex additive subgroup $H$, let $P_Hx$ be the simplest member of $x+H$, and
let $\rho_Hx=x-P_Hx$. The simplest member is unique because between two distinct
numbers of the same birthday lies an earlier number. Write $E_H$ for the set of these
representatives. The sum rule for cuts makes $P_H$ additive. At nested subgroups the
two projections compose to the projection at the larger subgroup.
[Simplest coset representatives](../Coset/Basic.lean)

Take $p\in E_H$ and a whole $w$. A product option formed from options $p',w'$ has gap

$$
pw-(p'w+pw'-p'w')=(p-p')(w-w').
$$

Every gap from $p$ to an earlier number lies outside $H$. Present $w$ by its defining
cut. Its gaps are $\pm1$, so every product gap still lies outside $H$. Thus $pw\in E_H$.
Now take $H=D$, a convex subring, and $0\ne w\in D$ whole. For $p\in E_D$ put
$q=P_D(p/w)$. Then $qw\in E_D$ and $p-qw\in D$. Uniqueness gives $p=qw$. Moreover
$q$ is whole, since $D$ contains the unit interval. In particular, $w$ divides $x$ in
wholes exactly when it divides $\rho_Dx$ there. For $D$ the finite surreals, this gives
$\omega/2\in\mathbf{Oz}$. [Exact division](Coset.lean#L90) ·
[Divisibility of the remainder](Divisibility.lean#L28)

Measure growth against $\Omega_i=\omega^{\omega^i}$. Write $C_i^-$ for the numbers whose
absolute values have every positive integer power below $\Omega_i$, and $C_i^+$ for
those bounded in magnitude by some integer power of $\Omega_i$. Class $i$ **occurs**
in $a$ when $P_{C_i^-}a\ne P_{C_i^+}a$. In decreasing order the occurring classes form
a well-ordered set. Their successive projections have strictly increasing birthdays
bounded by the birthday of $a$. A whole number with no occurring class is an ordinary
integer. For an ordinary integer divisor the test above reduces refinement to the usual
integer calculation on the finite remainders.
[Growth classes](../Scale/Growth.lean) · [Integer divisors](Refinement/Integer.lean)

At any occurring $i$ put $D=C_i^+$ and $w=\rho_Da$. Then $w\ne0$. Exact division gives
$a=wv$ with $v=1+(P_Da)/w$. The occurring classes of $v$ are precisely those of $a$
strictly above $i$. At and below $D$ its remainder is $1$. At larger classes,
multiplication and division by $w$ preserve the simplest representatives at both boundaries.
Thus $v$ has a strictly shorter initial segment of the original well-order.
[The complementary divisor](GrowthInduction.lean#L28)

It suffices to refine the four remainders in wholes at one occurring class. Indeed,
such a refinement gives $w=ef$ with $e\mid\rho_Dc$ and $f\mid\rho_Dd$. By the test,
$c=ec'$ and $d=fd'$ in wholes. Cancel $ef$ to get $vb=c'd'$. By induction write
$v=uv'$, $c'=ut$, $d'=v'k$, $b=tk$. Thus $(eu,fv',t,k)$ give the four required factors. [Induction from one class](Refinement/AtScale.lean#L42)

## The least bounded row

Suppose the occurring classes have a least member $i$. Put $C=C_i^-$ and $D=C_i^+$.
Let $B$ consist of the infinitesimals relative to $C$ (zero and the nonzero $x$ with
$1/x\notin C$). The product-gap formula makes $U=E_B$ a ring. Its members in $C$ form a
field $K$. Indeed, for $0\ne k\in U\cap C$, its inverse belongs to $C$ and
$1-kP_B(1/k)\in U\cap B=\lbrace 0\rbrace$. Taking $\rho_D$ on $U$ is a ring map into $V=U\cap D$, so the remainders still satisfy
$ab=cd$. Write $(a,c)$ and $(d,b)$ for the projected points.
[Representatives and scalars](../Coset/ResidueField.lean) · [The bounded ring](../Scale/Bounded/Basic.lean)

To compare the sizes of two entries, put $m_t=\omega^t$. Choose $t$ simplest modulo the
exponents of monomials that are units of $C$. Each nonzero $x$ has a unique **leading level**
$\lambda(x)$ for which $x/m_{\lambda(x)}$ and its inverse both lie in $C$. The **reading**
of $x$ at precision $t$ is $H_tx=P_B(x/m_t)$. At the leading level this is a nonzero
element of $K$. Levels add under multiplication. Nonzero members of $V$ have nonnegative
level. [Leading levels](../Scale/Basic.lean#L195) · [Readings](../Scale/Rounding.lean#L28)

Consider all $(f,g)\in V^2$ on $cf=ag$ with $f\ne0$. Suppose for a moment that one
has the least possible $\lambda(f)$. Divide both entries by the leading reading of $f$
so that it becomes $1$. This specifies the row uniquely. Two normalized rows at that
level would have a difference on the same line, with smaller horizontal level unless
their horizontal entries agreed. The line equation then forces their vertical entries to agree.

Now take any bounded point $(x,y)$ on the line. Round the quotient $q=P_B(x/f)$ and
subtract $q(f,g)$. The quotient is bounded since $1/f\in C$, and rounding keeps it
bounded. The difference is again on the line. Its horizontal entry divided by $f$ is
$x/f-q\in B$, so a nonzero horizontal remainder would have strictly smaller level.
Consequently $(x,y)=q(f,g)$.[^quotient] In the opening example, at $\Omega_0=\omega$, the row
is $(1,r)$. Its leading level is zero, and the two quotients are $\omega$ and $s$.
[Uniqueness](../Scale/Bounded/LeastRow.lean#L248) ·
[The exact rounded quotient](../Scale/Bounded/LeastRow.lean#L177)

## Why the minimum is attained

A bounded point can have infinitely many terms. Any finite list of such points nevertheless
has polynomial expressions in finitely many of their own readings. The coefficients belong
to the ring $L$ of finite sums of bounded monomials of nonnegative level with coefficients
in $K$.

The prefix selected at precision $t\ge0$ is $L_tx=P_{m_tB}x=m_tH_tx$. Reading twice
adds the precisions. To read a product $xy$, consider the levels $u,v$ of its factors’
gaps to earlier numbers. If some $u+v\lt t$, take $p\gt u$, $q\gt v$ with $p+q=t$. The shorter
prefixes $x_1=L_px$, $y_1=L_qy$ have smaller birthdays. The discarded product
$(x-x_1)(y-y_1)$ lies in $m_tB$, giving

$$
H_t(xy)=H_t(x_1y)+H_t(xy_1)-H_t(x_1y_1).
$$

Otherwise every $t-v$ lies below or at every $u$. Take a cut between these bounds
(the common endpoint in case of equality), clamped to $[0,t]$. Its value $p$ gives
$L_px=x$, $L_{t-p}y=y$, and $H_t(xy)=H_px\cdot H_{t-p}y$. Birthday induction now
expresses each product reading in monomials and readings of the factors.
[Product induction](../Scale/RoundedProduct.lean#L103)

Order the inputs, and for each input order its readings by decreasing precision. Keep
a reading when it lies outside the algebra of its predecessors.

1. **A missing reading has a greatest missing precision.** Take the supremum $t$ of the
   missing precisions in the bounded scale. Just below $t$, the discarded part $x-L_tx$
   still has level below the precision, so $H_ux=m_{t-u}H_tx$ there. If $H_tx$ were in
   the algebra, this entire interval would be present. At $t=0$ the assertion is immediate.
   [Suprema of precisions](../Scale/Bounded/Precision.lean#L170) ·
   [Greatest missing reading](../Scale/Bounded/Recovery.lean#L91)
2. **Each reading $X$ kept is transcendental over its predecessors.** All positive readings
   of $X$ belong to the preceding algebra. Given a relation of least degree $d$, read it
   where its leading coefficient becomes a nonzero scalar and divide by that scalar.
   Write $c$ for the next coefficient of this monic relation. At positive precision the
   leading coefficient reads to zero and the next one reads to $H_tc+dH_tX$. The term
   $dH_tX$ comes from expanding $X^d-(X-L_sX)^d$ at a sufficiently small $0\lt s\lt t$.
   Minimality forces the new relation to vanish coefficient by coefficient. Thus every
   positive reading of $c+dX$ is zero. It is a scalar, since any nonscalar remainder
   would be detected at its own leading level. As $K$ has characteristic zero, this puts
   $X$ in the preceding algebra. [Reading powers](../Scale/RoundedPowers.lean#L65) ·
   [The minimal relation](../Scale/Bounded/Adjunction.lean#L105)

Any polynomial dependence would involve a last selected reading. Any input with readings
still missing from their algebra would have a first such input and a greatest missing
precision, whose reading would have been selected. Thus the selected readings are
independent and span all inputs, since $H_0x=x$. Only finitely many occur in polynomial
expressions for the given list. [Selection of readings](../../Mathlib/Polynomial/OrderedReadings.lean#L84)

Start with the single product $ac\ne0$. Its polynomial uses finitely many readings.
For any $uv=ac$, add $u,v$ to the list after $ac$. The readings selected for $ac$ keep
their places. Degrees in each variable add in a nonzero product, so every variable in
$u$ or $v$ already occurs in $ac$. In particular, $a,c$ belong to this one polynomial
algebra over $L$. The coefficient exponents in their expressions generate a finite-rank
lattice $\Gamma$. In lattice coordinates a common monomial shift makes the powers in
both polynomials nonnegative. Their line equation is unchanged.
[Divisors of one product](../Scale/Bounded/LeastRow.lean#L124)

Let $A,C$ be the two polynomials after this shift. Divide both by their greatest common
divisor $d$, writing $A=dF$ and $C=dG$. For any polynomial point with $CX=AY$,
cancelling $d$ gives $GX=FY$. Since $F$ and $G$ are relatively prime, $F$ divides $X$.
Write $X=QF$. Cancelling $F$ gives $Y=QG$. Thus $(F,G)$ generates the polynomial
points on the line. This uses the usual gcd in a polynomial ring over a field.
[The gcd argument](../../Mathlib/FourFactorRefinement.lean#L61)

A second point $(x,y)$ can use exponents outside $\Gamma$. Group its terms by cosets of
$\Gamma$. Multiplication by $a$ or $c$ adds only exponents in $\Gamma$, so $cx=ay$ holds
within each coset separately. Translate each piece back into the lattice and clear its
negative coordinates by a monomial. The same $(F,G)$ works on each piece. Undo the
translations and add their multipliers. If $(x,y)$ uses new independent readings, compare
the coefficients of each monomial in the new variables in the same way.
[Exponent cosets](../../Mathlib/AddMonoidAlgebra/GeneratingRows.lean#L122) ·
[Additional variables](../../Mathlib/Polynomial/GeneratingRows.lean#L44)

The lattice calculation allows signed exponents. Shift the row by the negative of the
smallest coefficient exponent in either entry. Both entries now have nonnegative
coefficient exponents and at least one starts at zero. The least exponents in a nonzero
product add, so the multiplier of a bounded point also has nonnegative coefficient
exponents. The row therefore generates the line in $V$. For every nonzero multiplier $q$
in this ring, $\lambda(qf)=\lambda(q)+\lambda(f)\ge\lambda(f)$. This proves attainment.
Dividing by the leading reading of $f$ gives the unique normalized row, independent of the
coordinates used to find it. For $c=0$ the row is $(1,0)$.
[Monomial shift](../../Mathlib/AddMonoidAlgebra/GeneratingRows.lean#L296) ·
[Least bounded row](../Scale/Bounded/LeastRow.lean#L299)

When $a$ and $c$ are nonunits and $ac\ne0$, **one positive prefix of $ac$ suffices**.
Indeed, the variable $ac$ itself cannot be one of the independent generators in its
polynomial expression, since a polynomial variable cannot split into two nonunits.
The finitely many readings needed for its divisors therefore have positive precision.
Choose a positive precision at most their minimum, or any positive precision if the
list is empty. Reading that prefix again supplies every required reading. Since $f$
divides $a$ and $g$ divides $c$, both row entries belong to the resulting algebra
over $L$. The ordered pair $(a,c)$ specifies which line to take.
[Divisors from one prefix](../Scale/Bounded/Prefix.lean#L116)

## When there is no least class

Let $I$ be the classes occurring in $a$ and put $C=\bigcap_{i\in I}C_i^-$. Define
$B,U,K$ from $C$ as before. In $U$ identify two elements if their difference belongs
to $J=\bigcup_{t\gt 0}m_tU$, where $t$ ranges over the chosen exponent representatives.
Passage to this quotient takes the **germ** of an element. An error in $J$ disappears
on taking the remainder at some occurring class and at every lower one.
[Germs](../Germ/Basic.lean) · [The germ ideal at a limit](../Scale/Limit.lean#L36)

Read the four entries in this quotient, using the germ of each $H_tx$. The same selection
argument gives finite polynomial coordinates over $K$. Here a nonzero germ reading at
$s\lt t$ forces the prefix at $s$ to be born later than the prefix at $t$. Choosing a missing
reading of earliest prefix birthday therefore gives the greatest missing precision.
The minimal-degree argument applies to the germ readings, giving independence as before.
[Germ recovery](../Germ/Basic.lean#L262) · [Germ relations](../Germ/Readings.lean#L101)

Refine the four germs by the polynomial calculation and lift the factors to $U$.
Each of the four desired equations now has an error in $J$. Choose an occurring class
where each error disappears and take the least of these four classes. At that class all four equations are exact.
[Four equalities at one class](Refinement/Limit.lean#L51)

## Making the row and its multipliers whole

In both cases the projected entries are whole. At the common lower ring
$C=\bigcap_{i\in I}C_i^-$, the remainder of $a$ is an ordinary integer. Otherwise an
infinite remainder would have a growth class below every member of $I$ that itself
occurred in $a$. Taking $\rho_C$ on $U$ is a ring map into $K$. The lower matrix
therefore has whole entries in $K$ and an ordinary integer in its upper left corner.
Integer refinement and exact division give it a whole row and whole multipliers.
If the lower matrix is nonzero, any two row-column decompositions over $K$ differ by
a scalar on the row and its inverse on the column. Apply that scalar to the bounded
factors. Their lower remainders are now whole, which makes the factors whole too.
[The integer remainder](../Scale/Limit.lean#L114) ·
[Whole rescaling](Rescaling.lean#L137)

If the lower matrix is zero, one of the two vectors has zero lower remainder. Call
that vector $(q_j)$ and the other $(p_i)$. We seek $t$ such that every $m_tp_i$ and
$q_j/m_t$ is purely infinite or zero. Write $\ell(d)$ for the leading monomial exponent
of $d\ne0$. The conditions on $t$ are exactly

$$
-\ell(p_i-p')<t<\ell(q_j-q')
$$

for all $p',q'$ born earlier than the corresponding entries. Each gap from $q_j$ lies
outside $C$, and the reciprocal of each gap from $p_i$ lies in $C$. The product of
any two such gaps is infinite in magnitude. Hence every left bound is strictly below
every right bound, and their Conway cut supplies $t$. The rescaled factors also stay
in $D$, since a nonzero whole factor has magnitude at least one. The zero matrix itself
has a zero refinement. [The cut between the gaps](../Scale/OptionGaps.lean#L99)

In the opening example this is the passage from the bounded row $(1,r)$ to the whole
row $(m,rm)$, and from the column $(\omega,s)$ to $(\omega/m,s/m)$. The bounded row
serves every bounded point of its line. The whole rescaling only needs to serve the
two given points. In the general case the rescaling gives a whole split at one occurring
class. Dividing out that part of $a$ leaves the shorter list of classes required for induction.

In particular, every irreducible omnific integer is prime. If an irreducible $p$ divides
$cd$, write $pb=cd$ and refine. Of the two factors of $p$, one divides $c$ and the other
divides $d$. Since one of them is a unit, $p$ divides $c$ or $d$.
[The theorem](Refinement.lean#L61) · [Lean examples](../../Test/OmnificRefinement.lean)

[^quotient]: Evaluate two polynomials at a nonzero representative whose inverse is
    infinitesimal relative to their coefficient field. The remainder in polynomial
    division has lower degree than the divisor, so the ratio of their values is
    infinitesimal. Rounding the ratio of the original values gives the polynomial
    quotient evaluated at the same point.
    [Polynomial division by rounding](../Coset/PolynomialDivision.lean#L104)
