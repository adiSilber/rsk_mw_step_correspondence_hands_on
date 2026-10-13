import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.MW1_t
import LeanProof.MW1_u
import LeanProof.MW2_t

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false

/-!
# Mœglin–Waldspurger, part 2: proofs

The leading chain of `MW2_t` is the greedy chain of `MW1_u` (`leadingChain_eq`), which is what
the propositions reason about.
-/

namespace MW

lemma leadingChain_eq (m : Multisegment) (hm : m.segments ≠ []) :
    leadingChain m hm = (greedyChain m).val.segments := by
  unfold leadingChain
  exact segments_of_leadingIndices m (first_mem _ _) _

end MW
