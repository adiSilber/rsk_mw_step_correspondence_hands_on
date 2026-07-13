import LeanProof.Basic_t
import LeanProof.Basic_u
import LeanProof.RSK_t
import LeanProof.RSK_u
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
-- import Mathlib.Data.Set.Finite


set_option linter.style.setOption false
set_option linter.flexible false
set_option linter.style.whitespace false
set_option linter.hashCommand false

-- [(1,3), (2,4), (3,5)] — each consecutive pair is ≪ — ladder
#eval decide (isLadder
  [(⟨⟨1, 3⟩, by omega⟩ : Segment), ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩])
-- [(1,3), (1,4)] — a's are equal — not a ladder
#eval decide (isLadder
  [(⟨⟨1, 3⟩, by omega⟩ : Segment), ⟨⟨1, 4⟩, by omega⟩])
-- [(1,3), (2,4), (5,7)] — ladder (gaps are fine)
#eval decide (isLadder
  [(⟨⟨1, 3⟩, by omega⟩ : Segment), ⟨⟨2, 4⟩, by omega⟩, ⟨⟨5, 7⟩, by omega⟩])

-- m = [(1,3), (2,4), (3,5)] — sorted, and itself a ladder
-- depth (1,3) = 2, depth (2,4) = 1, depth (3,5) = 0
def m_ladder : Multisegment :=
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩], by decide⟩

#eval depth_of_segment m_ladder ⟨⟨1, 3⟩, by omega⟩ (by decide)
#eval depth_of_segment m_ladder ⟨⟨2, 4⟩, by omega⟩ (by decide)
#eval depth_of_segment m_ladder ⟨⟨3, 5⟩, by omega⟩ (by decide)

-- m = [(1,3), (1,4), (2,5)] — sorted lex, but (1,3) and (1,4) share an `a`
-- depth (1,3) = 1 — chain [(1,3), (2,5)] (skips (1,4) since the `a`'s tie)
-- depth (1,4) = 1 — chain [(1,4), (2,5)]
-- depth (2,5) = 0
def m_mixed : Multisegment :=
  ⟨[⟨⟨1, 3⟩, by omega⟩, ⟨⟨1, 4⟩, by omega⟩, ⟨⟨2, 5⟩, by omega⟩], by decide⟩

#eval depth_of_segment m_mixed ⟨⟨1, 3⟩, by omega⟩ (by decide)
#eval depth_of_segment m_mixed ⟨⟨1, 4⟩, by omega⟩ (by decide)
#eval depth_of_segment m_mixed ⟨⟨2, 5⟩, by omega⟩ (by decide)


-- m_ladder = [(1,3), (2,4), (3,5)] (itself a ladder).
-- For (1,3): sublists starting with it that are ladders are [(1,3)], [(1,3),(2,4)],
--           [(1,3),(3,5)], [(1,3),(2,4),(3,5)] → lengths {1, 2, 2, 3}.
#eval validLadderLengths m_ladder ⟨⟨1, 3⟩, by omega⟩
-- For (2,4): [(2,4)], [(2,4),(3,5)] → lengths {1, 2}.
#eval validLadderLengths m_ladder ⟨⟨2, 4⟩, by omega⟩
-- For (3,5): only [(3,5)] → {1}.
#eval validLadderLengths m_ladder ⟨⟨3, 5⟩, by omega⟩

-- m_mixed = [(1,3), (1,4), (2,5)].
-- For (1,3): [(1,3),(1,4)] is not a ladder (a's tie); valid sublists are
--           [(1,3)] and [(1,3),(2,5)] → lengths {1, 2}.
#eval validLadderLengths m_mixed ⟨⟨1, 3⟩, by omega⟩
-- For (1,4): [(1,4)] and [(1,4),(2,5)] → lengths {1, 2}.
#eval validLadderLengths m_mixed ⟨⟨1, 4⟩, by omega⟩


-- A base ladder [(2,4), (3,5)]: sorted, each consecutive pair satisfies ≪.
def base_ladder : Ladder :=
  ⟨⟨[⟨⟨2, 4⟩, by omega⟩, ⟨⟨3, 5⟩, by omega⟩], by decide⟩, by decide⟩

-- Prepend (1,3) ≪ (2,4): the new ladder is [(1,3), (2,4), (3,5)].
#eval (Ladder_extend base_ladder
    ⟨⟨2, 4⟩, by omega⟩
    ⟨⟨1, 3⟩, by omega⟩
    (by decide) (by decide)).val.segments


-- bucket m_ladder d (depths are 2, 1, 0 for (1,3), (2,4), (3,5)):
-- bucket 0 = [(3,5)], bucket 1 = [(2,4)], bucket 2 = [(1,3)]
#eval (bucket m_ladder 0).map (·.val)
#eval (bucket m_ladder 1).map (·.val)
#eval (bucket m_ladder 2).map (·.val)

-- bucket m_mixed d (depths are 1, 1, 0 for (1,3), (1,4), (2,5)):
-- bucket 0 = [(2,5)], bucket 1 = [(1,4), (1,3)], bucket 2 = []
#eval (bucket m_mixed 0).map (·.val)
#eval (bucket m_mixed 1).map (·.val)
#eval (bucket m_mixed 2).map (·.val)
