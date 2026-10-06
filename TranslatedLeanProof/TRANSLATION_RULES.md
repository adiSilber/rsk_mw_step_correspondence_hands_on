# Translating the tex into Lean

We translate one tex line at a time, in three phases. The translations themselves are in
`Basic.lean`, each preceded by its tex line and its identification.

---

## Phase 1: Identification

Before writing any Lean, answer three questions about the tex line.

### 1.1 Kind: `def` or `structure`?

- **`structure`**: the line introduces a **new kind of object** ("a segment is …").
- **`def`**: the line gives a **name to something built from objects we already have**
  ("we also write ⁻Δ = …").

One line can introduce several things (e.g. a segment *and* the notation `[a,b]`, *and*,
in parentheses, its length); each gets its own kind.

### 1.2 Symbols introduced before

List every symbol the line uses but does not define, with where it was introduced:
an earlier tex line, or standard math (ℤ, ≤, `+`, set-builder, ∅).
Include **implicit context**: letters bound by an earlier line (e.g. "Δ = [a,b]").
Write each symbol with the letters and the line where the tex introduces it.

### 1.3 New notation

For everything being defined: its **symbol** as the tex writes it (prefix, infix, brackets),
its **inputs**, and its **output**.

---

## Phase 2: Counterparts

Map every symbol from 1.2 to Lean:

- standard math ↦ Lean/Mathlib (ℤ ↦ `ℤ`, subset of ℤ ↦ `Set ℤ`, set-builder ↦ `{n : ℤ | …}`);
- an earlier tex line ↦ our translation of it;
- implicit letters (Δ = [a,b]) ↦ the fields of the object (`Δ.a`, `Δ.b`).

---

## Phase 3: Writing

1. **Notation defined by a formula** ↦ a `def` whose body is the formula, symbol by symbol,
   then a `notation` / `prefix` giving it the tex symbol.
2. **"An X is a Y of the form f(p) for some p with condition C"** ↦ a `structure` whose
   fields are the parameters p and the condition C; "is a Y" ↦ a coercion to Y given by f.
3. **"Note that …"** is a consequence, not part of the definition ↦ a `theorem` stated right
   after the definition.
4. **Doc comment** of each definition = the tex text it translates.
