import Hilbert14.ComparatorDefinitions
import Hilbert14.Theorem

/-! The counterexample in the standalone Comparator vocabulary. -/

namespace Hilbert14.Paper

/-- The displayed subfield has a polynomial intersection that is not finitely generated. -/
theorem counterexample : CounterexampleStatement :=
  Hilbert14.hilbert_fourteenth_counterexample

end Hilbert14.Paper

#print axioms Hilbert14.Paper.counterexample
