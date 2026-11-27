import PEqualNP.Defs

-- The search follows the live values needed by the output. It counts binary
-- gates and NOT gates separately and checks the remaining separating pairs.
-- The circuit translation and live-wire argument adapt L-meta-10363 and the
-- frontier search used for L-meta-19645.
namespace PEqualNP.Outside.L_meta_23794_Research

abbrev W := BitVec 100
abbrev Separators := BitVec 50

def goal : W := (BitVec.allOnes 50) ++ (0 : BitVec 50)

def binary (a b : W) : List W := [a &&& b, a ||| b]

def build : ℕ → Finset W → Prop
  | 0, s => goal ∈ s
  | k + 1, s =>
      build k s ∨
      (∃ a ∈ s, build k (insert (~~~a) s)) ∨
      ∃ a ∈ s, ∃ c ∈ s, a ≠ c ∧ ∃ z ∈ binary a c, build k (insert z s)

inductive Live : ℕ → ℕ → Finset W → Prop where
  | done (b n : ℕ) : Live b n {goal}
  | unary {b n : ℕ} {s r : Finset W} {a : W}
      (present : s = insert a r) (fresh : (~~~a) ∉ s)
      (tail : Live b n (insert (~~~a) r)) : Live b (n + 1) s
  | binary {b n : ℕ} {s r : Finset W} {a c z : W}
      (present : s = insert a (insert c r)) (different : a ≠ c)
      (op : z ∈ binary a c) (fresh : z ∉ s)
      (tail : Live b n (insert z r)) : Live (b + 1) n s

theorem liveWiden {b n B N : ℕ} {s : Finset W}
    (h : Live b n s) (hb : b ≤ B) (hn : n ≤ N) : Live B N s := by
  induction h generalizing B N with
  | done => exact .done _ _
  | unary present fresh _ ih =>
    cases N with
    | zero => omega
    | succ N => exact .unary present fresh (ih hb (by omega))
  | binary present different op fresh _ ih =>
    cases B with
    | zero => omega
    | succ B => exact .binary present different op fresh (ih (by omega) hn)

theorem liveCard {b n : ℕ} {s : Finset W} (h : Live b n s) : s.card ≤ b + 1 := by
  induction h with
  | done => simp
  | @unary b n s r a present fresh _ ih =>
    rw [present] at fresh ⊢
    have hn := Finset.card_insert_le a r
    rw [Finset.card_insert_of_notMem (fun member => fresh (Finset.mem_insert_of_mem member))] at ih
    omega
  | @binary b n s r a c z present _ _ fresh _ ih =>
    rw [present] at fresh ⊢
    have ha := Finset.card_insert_le a (insert c r)
    have hc := Finset.card_insert_le c r
    rw [Finset.card_insert_of_notMem (fun member => fresh
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem member)))] at ih
    omega

private theorem trim {z : W} {s t : Finset W} (ht : t ⊆ insert z s) (hn : ¬ t ⊆ s) :
    z ∉ s ∧ z ∈ t ∧ t.erase z ⊆ s := by
  have fresh : z ∉ s := by
    intro hz
    exact hn ((Finset.insert_eq_of_mem hz) ▸ ht)
  have need : z ∈ t := by
    by_contra miss
    apply hn
    intro u hu
    rcases Finset.mem_insert.mp (ht hu) with rfl | old
    · exact (miss hu).elim
    · exact old
  refine ⟨fresh, need, ?_⟩
  intro u hu
  obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hu
  exact (Finset.mem_insert.mp (ht mem)).resolve_left ne

theorem compress {k : ℕ} {s : Finset W} (h : build k s) :
    ∃ b n, b + n ≤ k ∧ ∃ t ⊆ s, Live b n t := by
  induction k generalizing s with
  | zero => exact ⟨0, 0, by omega, {goal}, Finset.singleton_subset_iff.mpr h, .done _ _⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, tail⟩ | ⟨a, ha, c, hc, ne, z, op, tail⟩
    · obtain ⟨b, n, hbn, t, ht, plan⟩ := ih skip
      exact ⟨b, n, by omega, t, ht, plan⟩
    · obtain ⟨b, n, hbn, t, ht, plan⟩ := ih tail
      by_cases sub : t ⊆ s
      · exact ⟨b, n, by omega, t, sub, plan⟩
      obtain ⟨fresh, need, remaining⟩ := trim ht sub
      let r := t.erase (~~~a)
      let u := insert a r
      have inside : u ⊆ s := Finset.insert_subset ha remaining
      refine ⟨b, n + 1, by omega, u, inside, .unary rfl (fun h => fresh (inside h)) ?_⟩
      simpa [r, Finset.insert_erase need] using plan
    · obtain ⟨b, n, hbn, t, ht, plan⟩ := ih tail
      by_cases sub : t ⊆ s
      · exact ⟨b, n, by omega, t, sub, plan⟩
      obtain ⟨fresh, need, remaining⟩ := trim ht sub
      let r := t.erase z
      let u := insert a (insert c r)
      have inside : u ⊆ s := Finset.insert_subset ha (Finset.insert_subset hc remaining)
      refine ⟨b + 1, n, by omega, u, inside, .binary rfl ne op (fun h => fresh (inside h)) ?_⟩
      simpa [r, Finset.insert_erase need] using plan

structure Cuts where
  ascending : Separators
  descending : Separators

def separators (w : W) : Cuts :=
  let negative := w.setWidth 50
  let positive := (w >>> 50).setWidth 50
  ⟨positive &&& ~~~negative, negative &&& ~~~positive⟩

def merge (l r : Cuts) : Cuts :=
  ⟨l.ascending ||| r.ascending, l.descending ||| r.descending⟩

def cuts (ws : List W) : Cuts :=
  ws.foldr (fun w rest => merge (separators w) rest) ⟨0, 0⟩

def enoughSeparation (n : ℕ) (c : Cuts) : Bool :=
  (if n = 0 then c.ascending else c.ascending ||| c.descending) == BitVec.allOnes 50

private theorem boolProductsMonotone : ∀ a b c d : Bool,
    a ≤ b → c ≤ d → (a && c) ≤ (b && d) ∧ (a || c) ≤ (b || d) := by decide

private def low (i : Fin 50) (w : W) : Bool := w.getLsbD i.val
private def high (i : Fin 50) (w : W) : Bool := w.getLsbD (i.val + 50)

private theorem goalSamples : ∀ i : Fin 50, high i goal = true ∧ low i goal = false := by
  decide +kernel

private theorem preserveSamples {b n : ℕ} {s : Finset W}
    (plan : Live b n s) (i : Fin 50) (rel : Bool → Bool → Prop)
    (meet : ∀ a b c d, rel a b → rel c d → rel (a && c) (b && d))
    (join : ∀ a b c d, rel a b → rel c d → rel (a || c) (b || d))
    (neg : n ≠ 0 → ∀ a b, rel a b → rel (!a) (!b))
    (seeds : ∀ w ∈ s, rel (high i w) (low i w)) : rel (high i goal) (low i goal) := by
  have lowFits : i.val < 100 := by omega
  have highFits : i.val + 50 < 100 := by omega
  induction plan with
  | done => exact seeds _ (Finset.mem_singleton_self _)
  | @unary b n s rest a present _ _ ih =>
    rw [present] at seeds
    apply ih (fun _ => neg (by omega))
    intro w member
    rcases Finset.mem_insert.mp member with rfl | old
    · have between := neg (by omega) _ _ (seeds a (Finset.mem_insert_self _ _))
      simpa only [low, high, BitVec.getLsbD_not, lowFits, highFits, decide_true, Bool.true_and]
        using between
    · exact seeds _ (Finset.mem_insert_of_mem old)
  | @binary b n s rest a c z present _ op _ _ ih =>
    rw [present] at seeds
    apply ih neg
    intro w member
    rcases Finset.mem_insert.mp member with rfl | old
    · have x := seeds a (Finset.mem_insert_self _ _)
      have y := seeds c (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      simp only [binary, List.mem_cons, List.not_mem_nil, or_false] at op
      rcases op with rfl | rfl
      · simpa only [low, high, BitVec.getLsbD_and] using meet _ _ _ _ x y
      · simpa only [low, high, BitVec.getLsbD_or] using join _ _ _ _ x y
    · exact seeds _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))

private theorem liveHasDifference {b n : ℕ} {s : Finset W}
    (plan : Live b n s) (i : Fin 50) : ∃ w ∈ s, high i w ≠ low i w := by
  classical
  by_contra none
  have same (w : W) (there : w ∈ s) : high i w = low i w := by
    by_contra different
    exact none ⟨w, there, different⟩
  have outputs := preserveSamples plan i Eq (fun _ _ _ _ => congrArg₂ Bool.and)
    (fun _ _ _ _ => congrArg₂ Bool.or) (fun _ _ _ => congrArg Bool.not) same
  rw [(goalSamples i).1, (goalSamples i).2] at outputs
  contradiction

private theorem liveHasAscent {b : ℕ} {s : Finset W}
    (plan : Live b 0 s) (i : Fin 50) : ∃ w ∈ s, high i w = true ∧ low i w = false := by
  classical
  by_contra none
  have order (w : W) (there : w ∈ s) : high i w ≤ low i w := by
    cases h : high i w <;> cases l : low i w
    · decide
    · decide
    · exact (none ⟨w, there, h, l⟩).elim
    · decide
  have outputs := preserveSamples plan i (fun a b => a ≤ b)
    (fun _ _ _ _ x y => (boolProductsMonotone _ _ _ _ x y).1)
    (fun _ _ _ _ x y => (boolProductsMonotone _ _ _ _ x y).2)
    (fun impossible => (impossible rfl).elim) order
  rw [(goalSamples i).1, (goalSamples i).2] at outputs
  exact (by decide : ¬((true : Bool) ≤ false)) outputs

private theorem ascendingBit (w : W) (i : Fin 50) :
    (separators w).ascending.getLsbD i.val = true ↔ high i w = true ∧ low i w = false := by
  simp [separators, high, low, i.isLt, Nat.add_comm]

private theorem descendingBit (w : W) (i : Fin 50) :
    (separators w).descending.getLsbD i.val = true ↔ high i w = false ∧ low i w = true := by
  simp [separators, high, low, i.isLt, Nat.add_comm, and_comm]

private theorem ascendingCuts (ws : List W) (i : Fin 50) :
    (cuts ws).ascending.getLsbD i.val = true ↔ ∃ w ∈ ws, high i w = true ∧ low i w = false := by
  induction ws with
  | nil => simp [cuts]
  | cons w rest ih =>
    change ((separators w).ascending ||| (cuts rest).ascending).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, ascendingBit]
    simp only [List.mem_cons]
    aesop

private theorem descendingCuts (ws : List W) (i : Fin 50) :
    (cuts ws).descending.getLsbD i.val = true ↔ ∃ w ∈ ws, high i w = false ∧ low i w = true := by
  induction ws with
  | nil => simp [cuts]
  | cons w rest ih =>
    change ((separators w).descending ||| (cuts rest).descending).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih, descendingBit]
    simp only [List.mem_cons]
    aesop

private theorem separated {b n : ℕ} {ws : List W} (plan : Live b n ws.toFinset) :
    enoughSeparation n (cuts ws) = true := by
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getElem_eq
  intro j hj
  rw [← BitVec.getLsbD_eq_getElem hj, BitVec.getElem_allOnes]
  let i : Fin 50 := ⟨j, hj⟩
  cases n with
  | zero =>
    obtain ⟨z, there, top, bottom⟩ := liveHasAscent plan i
    exact (ascendingCuts ws i).mpr ⟨z, List.mem_toFinset.mp there, top, bottom⟩
  | succ n =>
    obtain ⟨z, there, different⟩ := liveHasDifference plan i
    have mem := List.mem_toFinset.mp there
    change ((cuts ws).ascending ||| (cuts ws).descending).getLsbD i.val = true
    rw [BitVec.getLsbD_or, Bool.or_eq_true]
    cases top : high i z <;> cases bottom : low i z
    · exact (different (top.trans bottom.symm)).elim
    · exact Or.inr ((descendingCuts ws i).mpr ⟨z, mem, top, bottom⟩)
    · exact Or.inl ((ascendingCuts ws i).mpr ⟨z, mem, top, bottom⟩)
    · exact (different (top.trans bottom.symm)).elim

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))


theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))


def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind


private theorem retainedOne {ws rest : List W} {a : W} {needed : Finset W}
    (picked : ws.Perm (a :: rest)) (nd : ws.Nodup) (state : ws.toFinset = insert a needed) :
    ∃ kept, (kept = rest ∨ kept = a :: rest) ∧ kept.Nodup ∧ kept.toFinset = needed := by
  have orderly := picked.nodup_iff.mp nd
  have base : ws.toFinset = insert a rest.toFinset := by
    ext x
    simp [picked.mem_iff]
  have outside : ∀ x : W, x ∈ rest ↔ x ∈ needed ∧ x ≠ a := by
    intro x
    have change := congrArg (fun s : Finset W => x ∈ s) (base.symm.trans state)
    simp only [Finset.mem_insert, List.mem_toFinset] at change
    have away := (List.nodup_cons.mp orderly).1
    grind
  by_cases ha : a ∈ needed
  · refine ⟨a :: rest, Or.inr rfl, orderly, ?_⟩
    ext x
    simp only [List.mem_toFinset, List.mem_cons, outside]
    grind
  · refine ⟨rest, Or.inl rfl, (List.nodup_cons.mp orderly).2, ?_⟩
    ext x
    simp only [List.mem_toFinset, outside]
    grind

def accepts (b n : ℕ) (next : ℕ → ℕ → List W → Bool)
    (ws : List W) (z : W) (choices : List (List W)) : Bool :=
  !ws.contains z && choices.any (fun kept =>
    let front := z :: kept
    (front.length ≤ b + 1) && enoughSeparation n (cuts front) && next b n front)

def search : ℕ → ℕ → ℕ → List W → Bool
  | 0, _, _, ws => ws.contains goal
  | fuel + 1, b, n, ws =>
    ws.contains goal ||
    (n != 0 && (singles ws).any (fun (a, r) =>
      accepts b (n - 1) (search fuel) ws (~~~a) [r, a :: r])) ||
    (b != 0 && (pairs ws).any (fun (a, c, r) =>
      (binary a c).any (fun z => accepts (b - 1) n (search fuel) ws z (keepChoices a c r))))

theorem accepts_complete {b n : ℕ} {ws kept : List W} {choices : List (List W)} {z : W}
    {needed : Finset W} (next : ℕ → ℕ → List W → Bool)
    (fresh : z ∉ ws.toFinset) (inside : needed ⊆ ws.toFinset)
    (shape : kept ∈ choices) (nd : kept.Nodup) (eq : kept.toFinset = needed)
    (plan : Live b n (insert z needed))
    (complete : ∀ xs, xs.Nodup → xs.toFinset = insert z needed → next b n xs = true) :
    accepts b n next ws z choices = true := by
  have frontNd : (z :: kept).Nodup :=
    List.nodup_cons.mpr ⟨fun member => fresh (inside (eq ▸ List.mem_toFinset.mpr member)), nd⟩
  have frontEq : (z :: kept).toFinset = insert z needed := by simp [eq]
  have frontPlan : Live b n (z :: kept).toFinset := frontEq.symm ▸ plan
  have room := liveCard frontPlan
  rw [List.toFinset_card_of_nodup frontNd] at room
  have absent : ws.contains z = false :=
    Bool.eq_false_of_not_eq_true (fun h => fresh (List.mem_toFinset.mpr (List.contains_iff_mem.mp h)))
  have roomKept : kept.length ≤ b := by simpa using room
  simp only [accepts, absent, Bool.not_false, Bool.true_and, List.any_eq_true]
  exact ⟨kept, shape, by
    simp [roomKept, separated frontPlan, complete _ frontNd frontEq]⟩

theorem search_complete {b n : ℕ} {s : Finset W} (plan : Live b n s)
    (fuel : ℕ) (room : b + n ≤ fuel) (ws : List W) (nd : ws.Nodup) (state : ws.toFinset = s) :
    search fuel b n ws = true := by
  induction plan generalizing fuel ws with
  | @done b n =>
    have out : goal ∈ ws :=
      List.mem_toFinset.mp (state.symm ▸ Finset.mem_singleton_self _)
    cases fuel <;> simp [search, out]
  | @unary b n s r a present fresh _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have actual := state.trans present
      have ha : a ∈ ws :=
        List.mem_toFinset.mp (actual.symm ▸ Finset.mem_insert_self _ _)
      obtain ⟨rest, picked, perm⟩ := pick_one ha
      obtain ⟨kept, hk, keptNd, keptSet⟩ := retainedOne perm nd actual
      have inside : r ⊆ ws.toFinset := actual.symm ▸ Finset.subset_insert _ _
      have shape : kept ∈ [rest, a :: rest] := by simpa using hk
      have accepted := accepts_complete (search fuel) (state.symm ▸ fresh) inside
        shape keptNd keptSet (by assumption) (fun xs proper eq => ih fuel (by omega) xs proper eq)
      have direct : (singles ws).any (fun (a, rest) =>
          accepts b n (search fuel) ws (~~~a) [rest, a :: rest]) = true :=
        List.any_eq_true.mpr ⟨(a, rest), picked, accepted⟩
      simp [search, direct]
  | @binary b n s r a c z present different op fresh _ ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have actual := state.trans present
      have ha : a ∈ ws :=
        List.mem_toFinset.mp (actual.symm ▸ Finset.mem_insert_self _ _)
      have hc : c ∈ ws :=
        List.mem_toFinset.mp (actual.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      obtain ⟨rest, picked, perm⟩ := pick_two ha hc different
      have accepted {a c : W} (ordered : ws.Perm (a :: c :: rest))
          (same : ws.toFinset = insert a (insert c r)) :
          accepts b n (search fuel) ws z (keepChoices a c rest) = true := by
        obtain ⟨kept, shape, keptNd, keptSet⟩ := recover_kept ordered nd same
        have inside : r ⊆ ws.toFinset := by
          rw [same]
          exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
        exact accepts_complete (search fuel) (state.symm ▸ fresh) inside shape keptNd keptSet
          (by assumption) (fun xs proper eq => ih fuel (by omega) xs proper eq)
      have direct : (pairs ws).any (fun (a, c, rest) =>
          (binary a c).any (fun z => accepts b n (search fuel) ws z (keepChoices a c rest))) = true := by
        apply List.any_eq_true.mpr
        rcases picked with direct | reverse
        · exact ⟨(a, c, rest), direct, List.any_eq_true.mpr ⟨z, op, accepted perm actual⟩⟩
        · have swapped : ws.toFinset = insert c (insert a r) := by rw [actual, Finset.insert_comm]
          have flipped : z ∈ binary c a := by simpa [binary, BitVec.and_comm, BitVec.or_comm] using op
          exact ⟨(c, a, rest), reverse, List.any_eq_true.mpr
            ⟨z, flipped, accepted (perm.trans (.swap _ _ _)) swapped⟩⟩
      simp [search, direct]

namespace Translation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 100 || w.any (fun u => z == u ||
    (z == ~~~u || w.any (fun v => z == (u &&& v) || z == (u ||| v))))

private def bit (k : Fin 100) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 100) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr (.inr ⟨y, hy, .inl rfl⟩)⟩
    · exact .inr ⟨x, hx, .inr (.inr ⟨y, hy, .inr rfl⟩)⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem complement {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws (~~~x) := by
  rcases hx with rfl | hx
  · rw [show ~~~(0 : W) = BitVec.allOnes 100 by decide]
    simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inr (.inl rfl)⟩

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨BitVec.allOnes 100, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨BitVec.allOnes 100, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, complement (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, complement (mem i),
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 100 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 100 ∨ z ∈ available ∨
    (∃ a ∈ available, z = ~~~a) ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ binary a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 100 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 100 ∨ t ∈ available ∨
      (∃ a ∈ available, t = ~~~a) ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ binary a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · exact .inr (.inl (by decide))
    · exact .inl (by decide)
    · exact .inr (.inr (.inr (.inl ⟨x, hu, rfl⟩)))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [binary]⟩)))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [binary]⟩)))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 100) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 100 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    have freshOK : represents (insert z av) (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact (hw _ old).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all
    rcases classify hw hz with h | h | h | ⟨a, ha, rfl⟩ | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · exact Or.inr (.inl ⟨a, ha, fn _ freshOK he'⟩)
    · exact Or.inr (.inr ⟨a, ha, b, hb, hab, z, hop, fn _ freshOK he'⟩)

end Translation

def roots : List W := [
  ((33554431 : BitVec 50) ++ (0 : BitVec 50)),
  ((34326184928 : BitVec 50) ++ (108958055500899 : BitVec 50)),
  ((35150012382208 : BitVec 50) ++ (181596759168165 : BitVec 50)),
  ((1124800396230656 : BitVec 50) ++ (363193518336330 : BitVec 50)),
  ((33318502400 : BitVec 50) ++ (1016941851341724 : BitVec 50))]

def distinguishing (i : Fin 5) : Fin 50 :=
  ([24, 34, 25, 26, 37] : List (Fin 50)).get i

theorem exclusive : ∀ i j : Fin 5,
    high (distinguishing i) (roots.get j) ≠ low (distinguishing i) (roots.get j) → i = j := by
  unfold high low
  decide +kernel

theorem all_roots {b n : ℕ} {s : Finset W} (h : Live b n s) (sub : s ⊆ roots.toFinset) :
    s = roots.toFinset := by
  apply Finset.Subset.antisymm sub
  intro w hw
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp hw)
  obtain ⟨z, hz, same⟩ := liveHasDifference h (distinguishing i)
  obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (List.mem_toFinset.mp (sub hz))
  exact (exclusive i j same).symm ▸ hz

def tested (n : ℕ) : Bool :=
  enoughSeparation n (cuts roots) && search 6 (6 - n) n roots

set_option maxRecDepth 8000 in
set_option maxHeartbeats 10000000 in
theorem excluded : ∀ n : Fin 3, tested n.val = false := by decide +kernel

namespace Translation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cells : List (Fin 5 × Fin 5) := [
  (1, 2), (1, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 3), (2, 4), (3, 4), (4, 4),
  (1, 2), (1, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 3), (2, 4), (3, 4), (4, 4),
  (1, 2), (1, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 3), (2, 4), (3, 4), (4, 4),
  (1, 2), (1, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 3), (2, 4), (3, 4), (4, 4),
  (1, 2), (1, 3), (2, 4), (3, 4), (4, 4), (1, 2), (1, 3), (2, 4), (3, 4), (4, 4),
  (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 1), (0, 1), (0, 1), (0, 1), (0, 1),
  (0, 2), (0, 2), (0, 2), (0, 2), (0, 2), (0, 3), (0, 3), (0, 3), (0, 3), (0, 3),
  (0, 4), (0, 4), (0, 4), (0, 4), (0, 4), (1, 1), (1, 1), (1, 1), (1, 1), (1, 1),
  (1, 4), (1, 4), (1, 4), (1, 4), (1, 4), (2, 2), (2, 2), (2, 2), (2, 2), (2, 2),
  (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (3, 3), (3, 3), (3, 3), (3, 3), (3, 3)]

def samp (k : Fin 100) : Fin 5 × Fin 5 := cells.get k

def bitMask (i j : Fin 5) : Bool :=
  (275039 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)

def inputs (i j : Fin 5) : List Bool :=
  List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)

def agrees (C : Circuit) : Prop := ∀ i j : Fin 5, C.eval (inputs i j) = bitMask i j

theorem input_rows : ∀ k : Fin 100, roots.map (bit k) = inputs (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 100, bit k goal = bitMask (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : agrees C) (k : Fin 100) :
    (C.gates.foldl step (roots.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents roots.toFinset roots := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : FanInTwo C) (hr : agrees C) :
    build C.gates.length roots.toFinset :=
  compile C.gates C.output hg roots roots.toFinset initial_rep (rows_eval C hr)

end Translation

theorem no_six {C : PEqualNP.CircuitLowerBounds.Circuit}
    (hg : PEqualNP.MetaComplexity.FanInTwo C) (size : C.size ≤ 6)
    (hr : Translation.agrees C) : False := by
  obtain ⟨b, n, total, s, sub, hLive⟩ := compress (Translation.get_build C hg hr)
  rw [all_roots hLive sub] at hLive
  have count : roots.toFinset.card = 5 := by decide +kernel
  have fit := liveCard hLive
  rw [count] at fit
  change C.gates.length ≤ 6 at size
  have proper : roots.Nodup := by decide +kernel
  have widened : Live (6 - n) n roots.toFinset := liveWiden hLive (by omega) (by omega)
  have found : search 6 (6 - n) n roots = true :=
    search_complete widened 6 (by omega) roots proper rfl
  have accepted : tested n = true := by
    simp [tested, separated widened, found]
  have no : tested n = false := excluded ⟨n, by omega⟩
  rw [no] at accepted
  exact Bool.noConfusion accepted

end PEqualNP.Outside.L_meta_23794_Research

theorem PEqualNP.Outside.L_meta_23794_refutation :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 6 ∧
      ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) =
        (275039 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  rintro ⟨C, hg, size, hr⟩
  exact PEqualNP.Outside.L_meta_23794_Research.no_six hg size hr
