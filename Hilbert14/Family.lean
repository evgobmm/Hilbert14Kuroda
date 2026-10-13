import Hilbert14.Coordinates
import Hilbert14.Lemmas.FamilyCoefficient

/-!
# The polynomial family

The universal algebraic decomposition and recurrence of Kuroda's Lemma 2.2
construct polynomials in the field intersection for every natural index.
`exists_intersection_coefficient` gives a polynomial whose coefficient at that
index is the same fixed B³, where B represents (a+b)²−a³ in k[x,y]. A finite Taylor identity proves polynomiality,
and an injective scalar extension identifies the coefficient.
-/
