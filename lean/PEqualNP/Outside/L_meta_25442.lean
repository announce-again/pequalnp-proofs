import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25442

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def core (n base : ℕ) : List Gate :=
  [⟨.or, [n + 1, n + 2]⟩, ⟨.and, [0, base]⟩,
   ⟨.or, [n, n + 2]⟩, ⟨.and, [1, base + 2]⟩,
   ⟨.or, [n, n + 1]⟩, ⟨.and, [2, base + 4]⟩,
   ⟨.or, [base + 1, base + 3]⟩, ⟨.or, [base + 6, base + 5]⟩]

private def tail (n : ℕ) : List ℕ :=
  (List.range (n - 3)).map (fun i => i + 3) ++
    (List.range (n - 3)).map (fun i => n + (i + 3))

private def chain (cur : ℕ) : List ℕ → List Gate
  | [] => []
  | i :: is => ⟨.or, [cur, i]⟩ :: chain (cur + 1) is

private theorem chain_length (cur : ℕ) (is : List ℕ) :
    (chain cur is).length = is.length := by
  induction is generalizing cur with
  | nil => rfl
  | cons i is ih => simp [chain, ih]

private theorem core_mono (n base : ℕ) :
    Monotone2 ⟨core n base, 0⟩ := by
  intro g hg
  simp only [core, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

private theorem chain_mono (cur : ℕ) (is : List ℕ) :
    Monotone2 ⟨chain cur is, 0⟩ := by
  induction is generalizing cur with
  | nil => simp [chain, Monotone2]
  | cons i is ih =>
      intro g hg
      change g ∈ chain cur (i :: is) at hg
      rw [chain, List.mem_cons] at hg
      rcases hg with rfl | hg
      · simp
      · exact ih (cur + 1) g hg

private theorem bitOld (w extra : List Bool) (i : ℕ) (h : i < w.length) :
    (w ++ extra).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

private theorem bitNew (w extra : List Bool) (i : ℕ) :
    (w ++ extra).getD (w.length + i) false = extra.getD i false := by
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

private theorem bitFirst (w extra : List Bool) :
    (w ++ extra).getD w.length false = extra.getD 0 false := by
  simpa using bitNew w extra 0

private theorem chain_eval (x w : List Bool) (cur : ℕ) (is : List ℕ)
    (hcur : w.length = cur + 1) (hlen : x.length ≤ w.length)
    (hkeep : ∀ j < x.length, w.getD j false = x.getD j false)
    (hidx : ∀ j ∈ is, j < x.length) :
    (List.foldl step w (chain cur is)).getD (cur + is.length) false =
      (w.getD cur false || is.any fun j => x.getD j false) := by
  induction is generalizing w cur with
  | nil => simp [chain]
  | cons i is ih =>
      have hi : i < x.length := hidx i (by simp)
      let v := step w ⟨.or, [cur, i]⟩
      have hvlen : v.length = cur + 1 + 1 := by simp [v, step, hcur]
      have hvkeep (j : ℕ) (hj : j < x.length) :
          v.getD j false = x.getD j false := by
        dsimp only [v, step]
        rw [bitOld _ _ _ (by omega), hkeep j hj]
      have hvlast : v.getD (cur + 1) false = (w.getD cur false || x.getD i false) := by
        rw [← hcur]
        dsimp only [v, step]
        rw [bitFirst]
        simp only [List.getD_cons_zero, GateOp.eval, List.map_cons, List.map_nil,
          List.any_cons, List.any_nil, id, Bool.or_false, hkeep i hi]
      have ht (j : ℕ) (hj : j ∈ is) : j < x.length := hidx j (by simp [hj])
      change (List.foldl step v (chain (cur + 1) is)).getD (cur + (i :: is).length) false = _
      rw [show cur + (i :: is).length = cur + 1 + is.length by simp; omega]
      rw [ih v (cur + 1) hvlen (by omega) hvkeep ht, hvlast]
      simp [Bool.or_assoc]

private theorem fold_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (List.foldl step w gs).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      rw [List.foldl_cons, ih (step w g) (by simp [step]; omega)]
      exact bitOld _ _ _ hi

private theorem fold_length (gs : List Gate) (w : List Bool) :
    (List.foldl step w gs).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih, Nat.add_comm, Nat.add_left_comm]

private def low (a b : ℕ) : Bool :=
  ((decide (0 = a) && (decide (1 = b) || decide (2 = b))) ||
   (decide (1 = a) && (decide (0 = b) || decide (2 = b)))) ||
   (decide (2 = a) && (decide (0 = b) || decide (1 = b)))

private theorem row_bit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hi, Fin.ext_iff]

private theorem col_bit {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD (n + i) false = decide (i = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]

private theorem core_eval {n : ℕ} (hn : 4 ≤ n) (u v : Fin n) :
    (List.foldl step (oneEach u v) (core n (oneEach u v).length)).getD
      ((oneEach u v).length + 7) false = low u.val v.val := by
  let x := oneEach u v
  have hx : x.length = 2 * n := by simp [x, oneEach]; omega
  have h0 : 0 < x.length := by omega
  have h1 : 1 < x.length := by omega
  have h2 : 2 < x.length := by omega
  have hn0 : n < x.length := by omega
  have hn1 : n + 1 < x.length := by omega
  have hn2 : n + 2 < x.length := by omega
  have r0 := row_bit u v 0 (by omega)
  have r1 := row_bit u v 1 (by omega)
  have r2 := row_bit u v 2 (by omega)
  have c0 : (oneEach u v).getD n false = decide (0 = v.val) := by
    simpa only [Nat.add_zero] using col_bit u v 0 (by omega)
  have c1 := col_bit u v 1 (by omega)
  have c2 := col_bit u v 2 (by omega)
  change (List.foldl step x (core n x.length)).getD (x.length + 7) false = _
  simp only [core, List.foldl_cons, List.foldl_nil, step, GateOp.eval, List.map_cons,
    List.map_nil, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id,
    Bool.or_false, Bool.and_true, List.append_assoc, List.cons_append, List.nil_append,
    bitOld _ _ _ h0, bitOld _ _ _ h1, bitOld _ _ _ h2, bitOld _ _ _ hn0,
    bitOld _ _ _ hn1, bitOld _ _ _ hn2, bitNew, bitFirst]
  simp only [x, low, r0, r1, r2, c0, c1, c2, List.getD_cons_zero, List.getD_cons_succ]

private theorem tail_bound (n : ℕ) (i : ℕ) (hi : i ∈ tail n) : i < 2 * n := by
  simp only [tail, List.mem_append, List.mem_map, List.mem_range] at hi
  rcases hi with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩ <;> omega

private theorem tail_eval {n : ℕ} (u v : Fin n) :
    ((tail n).any fun i => (oneEach u v).getD i false) =
      (decide (3 ≤ u.val) || decide (3 ≤ v.val)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [tail, List.any_append, Bool.or_eq_true, List.any_map, Function.comp_apply,
    List.any_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro (⟨i, hi, hb⟩ | ⟨i, hi, hb⟩)
    · rw [row_bit u v (i + 3) (by omega), decide_eq_true_eq] at hb
      exact Or.inl (by omega)
    · rw [col_bit u v (i + 3) (by omega), decide_eq_true_eq] at hb
      exact Or.inr (by omega)
  · rintro (hu | hv)
    · refine Or.inl ⟨u.val - 3, by omega, ?_⟩
      rw [row_bit u v _ (by omega), decide_eq_true_eq]
      omega
    · refine Or.inr ⟨v.val - 3, by omega, ?_⟩
      rw [col_bit u v _ (by omega), decide_eq_true_eq]
      omega

private theorem base_table :
    ∀ a b : Fin 4,
      (low a.val b.val || (decide (3 ≤ a.val) || decide (3 ≤ b.val))) =
        (64478 : ℕ).testBit (4 * a.val + b.val) := by
  decide +kernel

private theorem pattern (a b : ℕ) :
    (low a b || (decide (3 ≤ a) || decide (3 ≤ b))) =
      (64478 : ℕ).testBit (4 * min a 3 + min b 3) := by
  let a' : Fin 4 := ⟨min a 3, by omega⟩
  let b' : Fin 4 := ⟨min b 3, by omega⟩
  have ha0 : (0 = a'.val) ↔ 0 = a := by dsimp [a']; omega
  have ha1 : (1 = a'.val) ↔ 1 = a := by dsimp [a']; omega
  have ha2 : (2 = a'.val) ↔ 2 = a := by dsimp [a']; omega
  have hb0 : (0 = b'.val) ↔ 0 = b := by dsimp [b']; omega
  have hb1 : (1 = b'.val) ↔ 1 = b := by dsimp [b']; omega
  have hb2 : (2 = b'.val) ↔ 2 = b := by dsimp [b']; omega
  have ha3 : 3 ≤ a'.val ↔ 3 ≤ a := by dsimp [a']; omega
  have hb3 : 3 ≤ b'.val ↔ 3 ≤ b := by dsimp [b']; omega
  simpa [low, ha0, ha1, ha2, hb0, hb1, hb2, ha3, hb3] using base_table a' b'

private theorem witness (n : ℕ) (hn : 4 ≤ n) :
    RepSizeAtMost (fun (u : Fin n) (v : Fin n) =>
      (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) (2 * n + 2) := by
  let gs := core n (2 * n)
  let ts := tail n
  let start := 2 * n + 7
  let C : Circuit := ⟨gs ++ chain start ts, start + ts.length⟩
  refine ⟨C, ?_, ?_, ?_⟩
  · intro g hg
    change g ∈ gs ++ chain start ts at hg
    rw [List.mem_append] at hg
    exact hg.elim (core_mono n (2 * n) g) (chain_mono start ts g)
  · change (gs ++ chain start ts).length ≤ 2 * n + 2
    simp [gs, ts, core, tail, chain_length]
    omega
  · intro u v
    let x := oneEach u v
    have hx : x.length = 2 * n := by simp [x, oneEach]; omega
    let w := List.foldl step x gs
    have hw : w.length = start + 1 := by
      change (List.foldl step x (core n (2 * n))).length = 2 * n + 7 + 1
      rw [fold_length, hx]
      rfl
    have hxl : x.length ≤ w.length := by omega
    have hkeep (j : ℕ) (hj : j < x.length) : w.getD j false = x.getD j false :=
      fold_keep gs x j hj
    have hidx (j : ℕ) (hj : j ∈ ts) : j < x.length := by
      rw [hx]
      exact tail_bound n j hj
    have hsmall : w.getD start false = low u.val v.val := by
      simp only [w, gs, start, ← hx]
      exact core_eval hn u v
    change (List.foldl step x (gs ++ chain start ts)).getD (start + ts.length) false = _
    rw [List.foldl_append, chain_eval x w start ts hw hxl hkeep hidx, hsmall]
    rw [show (ts.any fun i => x.getD i false) = _ from tail_eval u v]
    exact pattern u.val v.val

end PEqualNP.Outside.L_meta_25442

theorem PEqualNP.Outside.L_meta_25442 : (∀ n : ℕ, 4 ≤ n → PEqualNP.Represents.RepSizeAtMost (fun (u : Fin n) (v : Fin n) => (64478 : ℕ).testBit (4 * min u.val 3 + min v.val 3)) (2 * n + 2)) := by
  exact PEqualNP.Outside.L_meta_25442.witness
