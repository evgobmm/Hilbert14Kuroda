import Hilbert14.Lemmas.FractionCoordinates

/-!
# The coordinate automorphism

The automorphism x ↦ x⁻¹, y ↦ x⁵y, z ↦ z+x⁻¹ from equation (1) of
Kuroda's paper is defined on the polynomial ring with x inverted. Its
inverse sends x ↦ x⁻¹, y ↦ x⁵y, z ↦ z−x. `thetaEquiv` packages these
inverse maps; `theta` extends the automorphism to the fraction field.
-/
