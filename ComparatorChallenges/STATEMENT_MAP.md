# The counterexample and its Lean verification

The result is the explicit example with parameter $t_2=5$ in Section 4.1 of
[*Hilbert's fourteenth problem and field modifications*](https://arxiv.org/abs/1803.08002v1)
by Shigeru Kuroda.

[What is compared](#what-is-compared) · [The mathematical statement](#the-mathematical-statement) · [Correspondence with Lean](#correspondence-with-lean) · [Proof outline](#proof-outline)

## What is compared

There are two Lean files with different roles:

| File | Role |
|---|---|
| [ComparatorChallenges/Hilbert14.lean](Hilbert14.lean) | **Reference:** specifies the polynomial ring, fraction field, three generators, generated subfield and non-finite-generation statement. It imports only Mathlib. |
| [Hilbert14/ComparatorSolution.lean](../Hilbert14/ComparatorSolution.lean) | **Solution:** proves the statement using the full proof in this repository. Its definitions are in [Hilbert14/ComparatorDefinitions.lean](../Hilbert14/ComparatorDefinitions.lean); it does not import the reference. |

Both files declare `Hilbert14.Paper.counterexample` in **separate Lean environments**.
The [configuration](Hilbert14.json) tells Comparator which environments and theorem
to compare. The reference was written for this project.

The check has three parts:

1. **Statement:** Comparator checks that the solution proves the reference's
   proposition, including agreement of the mathematical definitions it uses.
2. **Proof:** Lean and the separately implemented Nanoda checker check the
   exported proof and its dependencies.
3. **Axioms:** the configuration permits only `propext`, `Quot.sound` and
   `Classical.choice`, the three standard logical axioms used here.

Comparator connects the formal reference to a checked proof. It does not read
the paper's prose; the mathematical correspondence is set out below. The reference's
intentional theorem placeholder specifies the task and is outside the solution's
import closure. See the [checking instructions](README.md).

## The mathematical statement

Here is the explicit counterexample in the notation of the formalization.
Let $x,y,z$ be algebraically independent variables over $\mathbb C$, and set

```math
a=x^5y+x^{-2},\qquad b=x^4y-x^{-2}+x^{-3},\qquad c=z+x^{-1}.
```

Inside $\mathbb C(x,y,z)$, define the **subfield** $L=\mathbb C(a,b,c)$ and
its polynomial intersection $A=L\cap\mathbb C[x,y,z]$. Then

```math
A\text{ is not finitely generated as a }\mathbb C\text{-algebra}.
```

This is a negative answer to Hilbert's fourteenth problem. Section 4.1 gives
the displayed field; the general construction is proved in Theorem 1.4 using
Lemma 2.2. The source code also proves this counterexample over every field of
characteristic zero. The standalone comparison targets the concrete complex-field
statement. Assertions about extension degrees and the fraction field of $A$
are not included.

## Correspondence with Lean

All reference definitions are in [Hilbert14.lean](Hilbert14.lean).

| Mathematical object or assertion | Lean definition |
|---|---|
| $k[x,y]$ | `Base k := MvPolynomial (Fin 2) k` |
| $k[x,y,z]$ | `Poly k := Polynomial (Base k)` |
| $k(x,y,z)$ | `Rat k := FractionRing (Poly k)` |
| Canonical inclusion of polynomials into rational functions | `embed k` |
| The three independent polynomial variables | `x k`, `y k`, `z k` |
| The three displayed rational functions | `a k`, `b k`, `c k` |
| Generated subfield $k(a,b,c)$ | `field k := IntermediateField.adjoin k {a k, b k, c k}` |
| Polynomial intersection $A$ | `intersection k := (field k).toSubalgebra.comap (embed k)` |
| Failure of finite algebra generation | `CounterexampleStatement := ¬ Algebra.FiniteType ℂ (intersection ℂ)` |

`IntermediateField.adjoin` closes under field operations and includes the scalar
field. `Subalgebra.comap` expresses the intersection in the polynomial ring via
the canonical embedding. `Algebra.FiniteType` is Mathlib's finite-generation
property for algebras. Neither an abstract substitute for $A$ nor an extra
mathematical assumption is introduced.

The solution derives the statement from
[`Hilbert14.hilbert_fourteenth_counterexample`](../Hilbert14/Theorem.lean).
The proof is organized into the [coordinate change](../Hilbert14/Coordinates.lean),
[field intersection](../Hilbert14/Intersection.lean),
[constant specialization](../Hilbert14/Specialization.lean),
[universal polynomial family](../Hilbert14/Family.lean), and
[finite-generation obstruction](../Hilbert14/Obstruction.lean).
Detailed arguments are in `Hilbert14/Lemmas/`. Every premise used by the final
assembly is supplied by those proofs.

## Proof outline

Write $P=k[x,y,z]$, $G=a$, $H=a+b$, and $B=H^2-G^3$.
The identity in [FamilyConcrete](../Hilbert14/Lemmas/FamilyConcrete.lean)
shows that $B$ is a polynomial in $k[x,y]$.

1. The coordinate automorphism sends the symmetric generators in
   $u=x$, $v=y-x+x^2$ to $a,b,c$. A swap argument and cancellation of
   prime-power denominators give the exact intersection
   $A=P\cap\theta(k[u+v,uv,z])$.
2. Specializing $y=0$ reduces this intersection to a shifted cusp algebra.
   In characteristic zero the resulting derivative constraint forces the
   specialization to be scalar. Thus every element of $A$ lies in $k+yP$.
3. The recurrence and finite Taylor identity construct, for every $n\in\mathbb N$,
   a polynomial $Q_n\in A$ whose coefficient of $z^n$ is $B^3$.
   [FamilyCoefficient](../Hilbert14/Lemmas/FamilyCoefficient.lean) proves this
   identity for all indices.
4. In the image of $A$ modulo $y^4$, every element is a scalar plus a nilpotent.
   Finite algebra generation would therefore imply finite module generation
   and a uniform bound on the $z$-coefficient support. But $B^3$ survives this
   quotient: setting $x=1$ makes its coefficient of $y^3$ equal to $1$.
   The family $Q_n$ contradicts the bound.

The quotient argument is proved in
[Obstruction](../Hilbert14/Lemmas/Obstruction.lean) and
[ObstructionCoefficient](../Hilbert14/Lemmas/ObstructionCoefficient.lean).
It applies to the coefficient quotient even though that ring has zero divisors.
