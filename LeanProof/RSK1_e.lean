import LeanProof.Basic_t
import LeanProof.Ladder2_t
import LeanProof.RSK1_t
import LeanProof.RSK1_u

set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

namespace RSK1Examples

-- m = [(1,100), (2,200), (3,90), (4,190), (5,80), (6,180)] (indices 0, …, 5)
-- depth 0: (2,200) ⊃ (4,190) ⊃ (6,180); depth 1: (1,100) ⊃ (3,90) ⊃ (5,80)
def m_complex : Multisegment :=
  ⟨[⟨⟨1, 100⟩, by omega⟩, ⟨⟨2, 200⟩, by omega⟩, ⟨⟨3, 90⟩, by omega⟩,
    ⟨⟨4, 190⟩, by omega⟩, ⟨⟨5, 80⟩, by omega⟩, ⟨⟨6, 180⟩, by omega⟩], by decide⟩

-- repeated segment: m = [(1,3), (1,3), (2,4)]; depth 1 = both copies of (1,3)
def m_repeated : Multisegment :=
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩], by decide⟩

/-! ### `enumeration`: our admissible enumeration of `𝔡⁻¹(k)` -/
#eval RSK.enumeration m_complex 0   -- [1, 3, 5]
#eval RSK.enumeration m_complex 1   -- [0, 2, 4]
#eval RSK.enumeration m_complex 2   -- [] (empty fiber)
#eval RSK.enumeration m_repeated 1  -- [0, 1] (equal segments: the first of [0,1], [1,0])
#eval RSK.enumeration ⟨[], by simp⟩ 0  -- [] (empty multisegment)

end RSK1Examples
