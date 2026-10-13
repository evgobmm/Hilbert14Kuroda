import Hilbert14.Coordinates
import Hilbert14.Lemmas.IntersectionFinal

/-!
# The field intersection

The coordinate change reduces the actual intersection to a polynomial invariant
algebra. `mem_intersection_iff_theta_symmetricAlgebra` and
`mem_intersection_iff_theta_Rz` apply to every element of the polynomial ring.
The proof uses the swap exchanging x and y−x+x², symmetric polynomials, and
prime-denominator cancellation.
-/
