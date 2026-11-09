/-
  Simple proofs about real numbers, with informal proofs alongside.

  NEEDS MATHLIB. The real numbers ℝ are not in core Lean, so this file
  will not work in the plain `hello` project. See the setup notes at the
  bottom of this file.

  Typing tips in VSCode:
    \R  → ℝ        \le → ≤       \ge → ≥       \ne → ≠
    \.  → ·        \ex → ∃       \and → ∧      \e  → ε     \d → δ

  The "power tools" you'll meet here:
    norm_num   : arithmetic with concrete numbers           (2 + 2 = 4, 1/2 + 1/3 = 5/6)
    ring       : algebraic identities, true by just expanding and collecting terms
    linarith   : linear inequalities/equations from your hypotheses
    nlinarith  : like linarith, but also multiplies hypotheses together (squares, products)
    positivity : goals of the form 0 < e or 0 ≤ e, by the shape of e
-/
import Mathlib

namespace RealDemo

/-
=====================================================================
  Example 1.  Arithmetic with actual numbers.
=====================================================================
  Note the `(2 : ℝ)`. Without it Lean would guess you mean natural numbers.
  On ℕ, 1/2 = 0 (integer division!), so the type really matters.
-/

example : (2 : ℝ) + 2 = 4 := by norm_num

example : (1 : ℝ) / 2 + 1 / 3 = 5 / 6 := by norm_num

-- Same expression in ℕ: 1/2 = 0 and 1/3 = 0, so the sum is 0. Ouch.
example : (1 : ℕ) / 2 + 1 / 3 = 0 := by norm_num


/-
=====================================================================
  Example 2.  Theorem: (a + b)² = a² + 2ab + b².
=====================================================================

  INFORMAL PROOF.
    (a + b)² = (a + b)(a + b)
             = a(a + b) + b(a + b)          (distribute on the right)
             = (a·a + a·b) + (b·a + b·b)    (distribute on the left)
             = a² + 2ab + b²                (ab = ba, collect terms)  ∎
-/

-- (A) Explicit: one named algebra law per step, using `calc`.
--     Each `_` means "the right-hand side of the previous line".
theorem sq_add_explicit (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  calc (a + b) ^ 2
      = (a + b) * (a + b)             := by rw [sq]           -- sq x : x ^ 2 = x * x
    _ = a * (a + b) + b * (a + b)     := by rw [add_mul]      -- (x + y) * z = x * z + y * z
    _ = (a * a + a * b) + (b * a + b * b) := by rw [mul_add, mul_add]  -- x * (y + z) = x * y + x * z
    _ = a ^ 2 + 2 * a * b + b ^ 2     := by ring              -- tidy up: commute and collect

-- (C) Short: `ring` proves any identity that holds in every commutative ring.
theorem sq_add_short (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring


/-
=====================================================================
  Example 3.  Theorem: if 2x + 1 = 7 then x = 3.
=====================================================================

  INFORMAL PROOF.
    Subtract 1 from both sides: 2x = 6. Divide by 2: x = 3.  ∎
-/

-- (A) Explicit-ish: name the intermediate fact with `have`, then compute.
theorem solve_linear_explicit (x : ℝ) (h : 2 * x + 1 = 7) : x = 3 := by
  have h2 : 2 * x = 6 := by linarith   -- "subtract 1 from both sides"
  calc x = (2 * x) / 2 := by ring      -- x = 2x/2  (true in ℝ, false in ℕ for odd x!)
    _ = 6 / 2          := by rw [h2]   -- substitute h2
    _ = 3              := by norm_num  -- arithmetic

-- (C) Short: linarith does all of the "move things across the = sign" work.
theorem solve_linear_short (x : ℝ) (h : 2 * x + 1 = 7) : x = 3 := by
  linarith


/-
=====================================================================
  Example 4.  Chaining inequalities.
=====================================================================

  INFORMAL PROOF.  a < b and b < c, so a < c (transitivity).  ∎
-/

-- (A) Explicit: cite the transitivity lemma by name.
theorem lt_chain_explicit (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c :=
  lt_trans hab hbc

-- (C) Short.
theorem lt_chain_short (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c := by
  linarith

-- linarith can combine several hypotheses at once:
-- from a ≤ b and c < d we get a + c < b + d.
example (a b c d : ℝ) (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  linarith


/-
=====================================================================
  Example 5.  Theorem (baby AM-GM): 2ab ≤ a² + b².
=====================================================================

  INFORMAL PROOF.
    Squares are nonnegative, so 0 ≤ (a − b)² = a² − 2ab + b².
    Add 2ab to both sides.  ∎

  This is the classic trick: the tactics won't invent the square (a − b)²
  for you, so you supply it as a hint.
-/

-- (A) Explicit: state the key fact, expand it, conclude linearly.
theorem two_mul_le_explicit (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have key : 0 ≤ (a - b) ^ 2 := sq_nonneg (a - b)       -- squares are ≥ 0
  have expand : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by ring
  rw [expand] at key                                     -- key : 0 ≤ a² − 2ab + b²
  linarith                                               -- add 2ab to both sides

-- (C) Short: hand nlinarith the hint, it does the rest.
theorem two_mul_le_short (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]


/-
=====================================================================
  Example 6.  Theorem: if 0 ≤ x ≤ 1 then x² ≤ x.
=====================================================================

  INFORMAL PROOF.
    x² = x · x ≤ 1 · x = x, where the middle step multiplies the
    inequality x ≤ 1 by the nonnegative number x.  ∎
-/

-- (A) Explicit. The middle step is the lemma
--     mul_le_mul_of_nonneg_right : b ≤ c → 0 ≤ a → b * a ≤ c * a
--     ("multiply both sides of an inequality by a nonnegative number").
theorem sq_le_self_explicit (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ x := by
  calc x ^ 2 = x * x := sq x
    _ ≤ 1 * x        := mul_le_mul_of_nonneg_right h1 h0
    _ = x            := one_mul x

-- (C) Short: nlinarith multiplies h0 and h1 together and finds it.
theorem sq_le_self_short (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 2 ≤ x := by
  nlinarith


/-
=====================================================================
  Example 7.  positivity: "obviously positive by its shape".
=====================================================================

  INFORMAL: a² ≥ 0 and b² ≥ 0 and 1 > 0, so a² + b² + 1 > 0.
-/

example (a b : ℝ) : 0 < a ^ 2 + b ^ 2 + 1 := by
  positivity

-- positivity uses the shape of the expression, not your hypotheses,
-- so for 0 < x * y with hypotheses hx, hy you cite a lemma instead:
example (x y : ℝ) (hx : 0 < x) (hy : 0 < y) : 0 < x * y :=
  mul_pos hx hy


/-
=====================================================================
  Example 8.  A first taste of analysis: ∃ and ε.
=====================================================================

  Theorem: for every ε > 0 there is a δ with 0 < δ < ε.

  INFORMAL PROOF.  Take δ = ε/2. Then δ > 0 since ε > 0,
  and δ = ε/2 < ε since ε > 0.  ∎

  Same pattern as Proof.lean: to prove ∃, supply the witness with
  `refine ⟨witness, ?_, ?_⟩` and then prove each remaining goal.
-/

theorem exists_smaller (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ δ < ε := by
  refine ⟨ε / 2, ?_, ?_⟩
  · positivity   -- goal: 0 < ε / 2
  · linarith     -- goal: ε / 2 < ε


/-
=====================================================================
  EXERCISES.  Replace each `sorry` with a proof.
  Try the explicit style first, then check yourself with a power tool.
=====================================================================
-/

-- 1. (Hint: Example 2.)
theorem ex1 (a b : ℝ) : (a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2 := by
  sorry

-- 2. (Hint: Example 3.)
theorem ex2 (x : ℝ) (h : 3 * x - 4 = 11) : x = 5 := by
  sorry

-- 3. If 0 < a < b then a² < b².
--    Informal hint: b² − a² = (b − a)(b + a), and both factors are positive.
theorem ex3 (a b : ℝ) (ha : 0 < a) (hab : a < b) : a ^ 2 < b ^ 2 := by
  sorry

-- 4. (Hint: Example 8. What δ makes 3δ < ε?)
theorem ex4 (ε : ℝ) (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ 3 * δ < ε := by
  sorry

-- 5. Challenge: a² + b² = 0 forces a = 0.
--    Informal hint: 0 ≤ a² ≤ a² + b² = 0, so a² = 0.
--    Useful lemma: pow_eq_zero_iff, or try nlinarith with hints.
theorem ex5 (a b : ℝ) (h : a ^ 2 + b ^ 2 = 0) : a = 0 := by
  sorry

end RealDemo


/-
=====================================================================
  SETUP: making a project that has Mathlib (one time, Windows)
=====================================================================

  Easiest way, from VSCode:
    1. Click the ∀ icon at the top right of a .lean file
       → "New Project..." → "Create Project Using Mathlib".
    2. Pick a folder (e.g. C:\Users\Anthony\lean-test) and a name (e.g. realproofs).
    3. Wait. It downloads a few GB of prebuilt Mathlib. This can take a while.
    4. Open that project folder in VSCode, drop this file in next to the
       generated .lean files, and open it. The first `import Mathlib`
       takes ~30 seconds to load.

  Or from the terminal (View → Terminal), in C:\Users\Anthony\lean-test :
    lake +leanprover-community/mathlib4:lean-toolchain new realproofs math
    cd realproofs
    lake exe cache get
    code .

  IMPORTANT: never skip `lake exe cache get`. Without it Lean tries to
  compile all of Mathlib from scratch, which takes hours.
-/
