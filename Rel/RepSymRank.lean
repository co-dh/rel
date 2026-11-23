module

public import Rel.Run.Table
public import Rel.RepAsc
public import Rel.RepWF
public import Rel.RepTabDiv
public import Rel.RepTabComp
public import Rel.RepStruct
public import Rel.RepCanon
public import Rel.RepSums
public import Rel.Lang.DfnLaw

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The law of `Table.symAsc` (`Rel/Run/Table.lean`) and the laws of `<` and `asc` at `sym` as terms (`Elab.symOrd`): they go through
the rank of the symbol's text (owner decision J), so they follow the order of the texts and not of the ids. -/

namespace Rel.Lang.Table

open Rel Rel.Rep

/-- **`rank` is `iasc(D)°`**: an id `i` of `D` goes to `r` when its text `t` is the `r`-th smallest text of `D`
(`ascDen` of `ran D`), `rank D = D ≫ asc(ran D)°`. -/
theorem rank_holds {D : Dict} {R : Tab .long .long} (h : rank D = .ok R) (wD : D.WF) (i r : Int64) :
    R.Holds i r ↔ ∃ t, D.Holds i t ∧ ascDen (.arr (.atom .char)) (fun u => ∃ i', D.Holds i' u) r t := by
  unfold rank at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S, hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T, hT, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  have wS := Tab.ran_wf hS wD
  have wT := Tab.asc_wf hT wS
  have wC := Tab.conv_wf hC wT
  have hp : (fun b => ∃ c, S.Holds b c) = fun u => ∃ i', D.Holds i' u := funext fun b => propext
    ⟨fun ⟨c, hc⟩ => ((Tab.ran_holds hS wD.2 b c).1 hc).2, fun h => ⟨b, (Tab.ran_holds hS wD.2 b b).2 ⟨rfl, h⟩⟩⟩
  have hA := Tab.asc_holds hT wS
  rw [hp] at hA
  rw [Tab.comp_holds h wD wC]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Tab.conv_holds hC wT, ← hA]
  rfl

/-- A `sym` column read as the `i64` column of the same words: each id is the word as an `Int64`. -/
theorem get_sym_i64 {n : USize} (v : Arr .sym n) (w : Arr .i64 n) (he : w.enc = v.enc) (i : Fin n.toNat) :
    w.get i = (v.get i).toInt64 := by
  rw [Arr.get_ne _ _ (by decide), Arr.get_ne _ _ (by decide), he]
  have h := v.wf
  generalize v.enc = e at h ⊢
  cases e <;> simp_all [Ext.Enc.WF, QAtomicType.width, Ext.Enc.get, Column.atomOfBits, Dep.Carrier.of?]

/-- The id of a `sym` read as the `i64` the rank table is keyed by. -/
theorem symIds_row {A : Obj} (I : Tab A (.atom .sym)) (i : Fin I.n.toNat) :
    (symIds I).val.row i = (I.val.row i).toInt64 := by
  unfold symIds
  rw [Vals.row_atom, Vals.row_atom]
  exact get_sym_i64 _ _ rfl i

/-- **`K ≫ rank`**: a symbol `a` of the column `K` goes to `r` when `a`'s id is `rank`'s `r`. -/
theorem symRanked_holds {w : String} {D : Dict} {n : USize} {K : Vals (.atom .sym) n} {P : Tab (.atom .sym) .long}
    {R : Tab .long .long} (h : symRanked w D K = .ok P) (hR : rank D = .ok R) (wR : R.WF) (a : UInt64) (r : Int64) :
    D.n.toNat < 2 ^ 63 ∧ (P.Holds a r ↔ (∃ i, K.row i = a) ∧ R.Holds a.toInt64 r) := by
  unfold symRanked at h
  simp only [Bind.bind, hR] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P0, hP0, h⟩ := h
  injection hP0 with e; subst e
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  have hQP : Q = P ∧ D.n.toNat < 2 ^ 63 := by
    by_cases c1 : Q.n = n <;> by_cases c2 : D.n.toNat < 2 ^ 63 <;>
      simp [c1, c2, pure, Except.pure, Except.bind] at h <;> exact ⟨h, c2⟩
  obtain ⟨rfl, hb⟩ := hQP
  have wI : (symIds (⟨n, K, K⟩ : Tab (.atom .sym) (.atom .sym))).WF := ⟨trivial, trivial⟩
  refine ⟨hb, ?_⟩
  rw [Tab.comp_holds hQ wI wR]
  constructor
  · rintro ⟨b, ⟨i, hi, hb⟩, hr⟩
    have hb' : b = a.toInt64 := by rw [← hb, ← hi]; exact symIds_row ⟨n, K, K⟩ i
    exact ⟨⟨i, hi⟩, hb' ▸ hr⟩
  · rintro ⟨⟨i, hi⟩, hr⟩
    exact ⟨a.toInt64, ⟨i, hi, by rw [← hi]; exact symIds_row ⟨n, K, K⟩ i⟩, hr⟩

/-- **Ranks order as their elements do**: two elements numbered by `asc`'s `ascDen` are in `Int64` order exactly
when they are in `B.lt` order, so long as the numbers do not wrap (`hb`: no ascending list of the set is `2^63` long). -/
theorem ascDen_lt {B : Obj} {p : B.El → Prop} {j₁ j₂ : Int64} {t₁ t₂ : B.El}
    (hb : ∀ ys : List B.El, ys.Pairwise B.lt → (∀ b, b ∈ ys ↔ p b) → ys.length < 2 ^ 63)
    (h₁ : ascDen B p j₁ t₁) (h₂ : ascDen B p j₂ t₂) : j₁ < j₂ ↔ B.lt t₁ t₂ := by
  obtain ⟨ys, hys, hm, k₁, e₁, rfl⟩ := h₁
  obtain ⟨ys', hys', hm', k₂, e₂, rfl⟩ := h₂
  obtain rfl : ys' = ys := lt_sorted_unique hys' hys fun b => (hm' b).trans (hm b).symm
  obtain ⟨l₁, rfl⟩ := List.getElem?_eq_some_iff.1 e₁
  obtain ⟨l₂, rfl⟩ := List.getElem?_eq_some_iff.1 e₂
  have hl := hb ys' hys' hm'
  have hi : Int64.ofNat k₁ < Int64.ofNat k₂ ↔ k₁ < k₂ := by
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofNat', Int64.toInt_ofNat', Int64.size, Int.bmod_eq_of_le (by omega) (by omega),
      Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  rw [hi]
  constructor
  · exact fun hk => List.pairwise_iff_getElem.1 hys' k₁ k₂ l₁ l₂ hk
  · intro h
    refine Nat.lt_of_not_le fun hk => ?_
    rcases Nat.lt_or_eq_of_le hk with hk' | rfl
    · exact B.lt_asymm h (List.pairwise_iff_getElem.1 hys' k₂ k₁ l₂ l₁ hk')
    · exact B.lt_irrefl _ h

/-- A list without repeats inside `L` is no longer than `L`. -/
theorem nodup_length_le {α : Type} [DecidableEq α] : ∀ (ys L : List α), ys.Nodup → ys ⊆ L → ys.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | a :: ys, L, hn, hs => by
    have ha : a ∈ L := hs (List.mem_cons_self ..)
    have hsub : ys ⊆ L.erase a := fun b hb =>
      (List.mem_erase_of_ne fun e => (List.nodup_cons.1 hn).1 (by subst e; exact hb)).2
        (hs (List.mem_cons_of_mem _ hb))
    have h1 := nodup_length_le ys (L.erase a) (List.nodup_cons.1 hn).2 hsub
    rw [List.length_erase_of_mem ha] at h1
    have h2 : 0 < L.length := List.length_pos_of_mem ha
    simp only [List.length_cons]; omega

/-- **`rank` orders ids by their texts**: for ids `i₁`, `i₂` of a dictionary `D` (one text per id, fewer than `2^63`
texts) with texts `t₁`, `t₂` and ranks `r₁`, `r₂`, `r₁ < r₂` iff `t₁` is before `t₂` in `Obj.lt` (the order of the
texts, `asc`'s), whatever the order the ids were inserted in. -/
theorem rank_lt_iff {D : Dict} {R : Tab .long .long} (h : rank D = .ok R) (wD : D.WF) (hb : D.n.toNat < 2 ^ 63)
    (hf : ∀ i t t', D.Holds i t → D.Holds i t' → t = t') {i₁ i₂ r₁ r₂ : Int64} {t₁ t₂ : (Obj.arr (.atom .char)).El}
    (h₁ : D.Holds i₁ t₁) (h₂ : D.Holds i₂ t₂) (hr₁ : R.Holds i₁ r₁) (hr₂ : R.Holds i₂ r₂) :
    r₁ < r₂ ↔ Obj.lt (.arr (.atom .char)) t₁ t₂ := by
  obtain ⟨u₁, hu₁, a₁⟩ := (rank_holds h wD _ _).1 hr₁
  obtain ⟨u₂, hu₂, a₂⟩ := (rank_holds h wD _ _).1 hr₂
  obtain rfl := hf _ _ _ h₁ hu₁
  obtain rfl := hf _ _ _ h₂ hu₂
  refine ascDen_lt (fun ys hys hm => ?_) a₁ a₂
  have hnd : ys.Nodup := hys.imp fun {a b} hab e => by subst e; exact Obj.lt_irrefl _ a hab
  have hsub : ys ⊆ List.ofFn (fun j : Fin D.n.toNat => D.val.row j) := fun b hb' => by
    obtain ⟨i', j, -, hj⟩ := (hm b).1 hb'
    exact List.mem_ofFn.2 ⟨j, hj⟩
  have := nodup_length_le ys _ hnd hsub
  simp only [List.length_ofFn] at this
  omega

/-- A table of atoms on both sides is well formed (`Vals.WF` holds of an atom column). -/
theorem atom_wf {t u : QAtomicType} (T : Tab (.atom t) (.atom u)) : T.WF := ⟨trivial, trivial⟩

/-- **`rank` is well formed** when `D` is. -/
theorem rank_wf {D : Dict} {R : Tab .long .long} (h : rank D = .ok R) (wD : D.WF) : R.WF := by
  unfold rank at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S, hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T, hT, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  exact Tab.comp_wf h wD (Tab.conv_wf hC (Tab.asc_wf hT (Tab.ran_wf hS wD)))

/-- **`hf` for a dictionary built by `frame`** (`Dict.empty`, `intern`, `readDict`): its key is the positions
`0 … n-1`, each id once, so an id has one text. `Dict` is an abbreviation of `Tab`, not a structure, so this is
the invariant of how a dictionary is made and no `D.WF` states it. -/
theorem frame_functional {B : Obj} {n : USize} {x : Vals B n} {D : Tab .long B} (h : frame x = .ok D) (i : Int64)
    (t t' : B.El) (h₁ : D.Holds i t) (h₂ : D.Holds i t') : t = t' := by
  unfold frame at h
  cases hP : Arr.pos n with
  | error e => rw [hP] at h; cases h
  | ok P =>
    rw [hP] at h; cases h
    obtain ⟨j, hj, rfl⟩ := h₁
    obtain ⟨j', hj', rfl⟩ := h₂
    have e := congrArg (fun x : Int64 => x.toBitVec.toNat)
      (((Arr.pos_get hP j).symm.trans hj).trans ((Arr.pos_get hP j').symm.trans hj').symm)
    have h1 : j.1 < n.toNat := j.2
    have h2 : j'.1 < n.toNat := j'.2
    have h3 := n.toNat_lt_size
    have h4 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> rw [h] <;> decide
    simp [Nat.toUInt64, UInt64.toInt64, Int64.toBitVec] at e
    obtain rfl : j = j' := Fin.ext (by omega)
    rfl

/-- **`asc` on `sym` numbers the set by rank**: `symAsc D P` holds `(j, a)` when `a` is in `dom P` and its rank
`r` is the `j`-th smallest of the ranks of `dom P` (`ascDen` at `ℕ`), so by `rank_lt_iff` the `j`-th smallest text. -/
theorem symAsc_holds {D : Dict} {Rk : Tab .long .long} {P : Tab (.atom .sym) (.atom .sym)}
    {T : Tab .long (.atom .sym)} (h : symAsc D P = .ok T) (hR : rank D = .ok Rk) (wD : D.WF) (wP : Vals.WF P.key)
    (j : Int64) (a : UInt64) :
    T.Holds j a ↔ (∃ y, P.Holds a y) ∧ ∃ r, Rk.Holds a.toInt64 r ∧
      ascDen .long (fun b => ∃ x, (∃ y, P.Holds x y) ∧ Rk.Holds x.toInt64 b) j r := by
  unfold symAsc at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S, hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨R', hR', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨CR, hCR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨A, hA, h⟩ := h
  have wRk := rank_wf hR wD
  have hRh := fun a r => (symRanked_holds hR' hR wRk a r).2
  have wR' := atom_wf R'
  have wC := Tab.conv_wf hC wR'
  have wCR := Tab.comp_wf hCR wC wR'
  have wA := Tab.asc_wf hA wCR
  have hAh : A.Holds = ascDen .long fun b => ∃ c, CR.Holds b c := Tab.asc_holds hA wCR
  have hp : (fun b => ∃ c, CR.Holds b c) = fun b => ∃ x, (∃ y, P.Holds x y) ∧ Rk.Holds x.toInt64 b :=
    funext fun b => propext
      ⟨fun ⟨c, hbc⟩ => by
        obtain ⟨x, hCx, hxc⟩ := (Tab.comp_holds hCR wC wR' b c).1 hbc
        obtain ⟨hd, hk⟩ := (hRh x b).1 ((Tab.conv_holds hC wR' b x).1 hCx)
        exact ⟨x, (Tab.dom_key hS wP x).1 hd, hk⟩,
       fun ⟨x, hy, hk⟩ => by
        have hxb := (hRh x b).2 ⟨(Tab.dom_key hS wP x).2 hy, hk⟩
        exact ⟨b, (Tab.comp_holds hCR wC wR' b b).2 ⟨x, (Tab.conv_holds hC wR' b x).2 hxb, hxb⟩⟩⟩
  rw [hp] at hAh
  rw [Tab.comp_holds h wA wC]
  constructor
  · rintro ⟨r, hAj, hCr⟩
    obtain ⟨hd, hk⟩ := (hRh a r).1 ((Tab.conv_holds hC wR' r a).1 hCr)
    exact ⟨(Tab.dom_key hS wP a).1 hd, r, hk, by rw [← hAh]; exact hAj⟩
  · rintro ⟨hd, r, hk, hasc⟩
    exact ⟨r, by rw [hAh]; exact hasc,
      (Tab.conv_holds hC wR' r a).2 ((hRh a r).2 ⟨(Tab.dom_key hS wP a).2 hd, hk⟩)⟩

/-- **`Obj.lt` at `long` is `Int64`'s `<`**: the key of `x` is its order code `x ^^^ 2^63` (a signed word's sign bit
flipped), and a one-element key list orders as its element. -/
theorem Obj.lt_long (x y : Int64) : Obj.lt .long x y ↔ x < y := by
  have key : ∀ x : Int64, Obj.key .long x = [(Kernel.ordCode 8 false true x.toUInt64).toNat] := fun _ => rfl
  have c : ∀ x : Int64, (Kernel.ordCode 8 false true x.toUInt64).toNat = (x.toInt + 2 ^ 63).toNat := fun x => by
    rw [ordCode_signed (by omega) (by omega)]
    have h3 := BitVec.toInt_eq_toNat_cond x.toBitVec
    have h4 := x.toBitVec.isLt
    have h2 : x.toUInt64.toNat = x.toBitVec.toNat := rfl
    simp only [Int64.toInt] at *
    split at h3 <;> omega
  unfold Obj.lt; rw [key, key, c, c]
  simp only [List.cons_lt_cons_iff, List.not_lt_nil, and_false, or_false]
  rw [Int64.lt_iff_toInt_lt]
  have h1 := Int64.le_toInt x; have h2 := Int64.toInt_lt x; have h3 := Int64.le_toInt y; have h4 := Int64.toInt_lt y
  omega

/-- **Each ascending list of ranks has an ascending list of texts of its length**: the rank `b` of `ys` is the rank
of an id `i` of `D`, whose text `z` is the one `rank_lt_iff` orders as `b` is. -/
theorem rank_texts {D : Dict} {R : Tab .long .long} (h : rank D = .ok R) (wD : D.WF) (hb : D.n.toNat < 2 ^ 63)
    (hf : ∀ i t t', D.Holds i t → D.Holds i t' → t = t') :
    ∀ ys : List Int64, ys.Pairwise (Obj.lt .long) → (∀ b ∈ ys, ∃ i, R.Holds i b) →
      ∃ zs : List (Obj.arr (.atom .char)).El, zs.length = ys.length ∧ zs.Pairwise (Obj.lt (.arr (.atom .char))) ∧
        ∀ z ∈ zs, ∃ b ∈ ys, ∃ i, R.Holds i b ∧ D.Holds i z
  | [], _, _ => ⟨[], rfl, List.Pairwise.nil, fun _ hz => nomatch hz⟩
  | a :: ys, hp, hm => by
    obtain ⟨hlt, hp'⟩ := List.pairwise_cons.1 hp
    obtain ⟨zs, hl, hz, hq⟩ := rank_texts h wD hb hf ys hp' fun b hb' => hm b (List.mem_cons_of_mem _ hb')
    obtain ⟨i, hi⟩ := hm a (List.mem_cons_self ..)
    obtain ⟨t, ht, -⟩ := (rank_holds h wD _ _).1 hi
    refine ⟨t :: zs, by simp [hl], List.pairwise_cons.2 ⟨fun z hz' => ?_, hz⟩, fun z hz' => ?_⟩
    · obtain ⟨b, hbm, i', hi', hd⟩ := hq z hz'
      exact (rank_lt_iff h wD hb hf ht hd hi hi').1 ((Obj.lt_long _ _).1 (hlt b hbm))
    · rcases List.mem_cons.1 hz' with rfl | hz'
      · exact ⟨a, List.mem_cons_self .., i, hi, ht⟩
      · obtain ⟨b, hbm, w⟩ := hq z hz'
        exact ⟨b, List.mem_cons_of_mem _ hbm, w⟩

/-- **`asc` on `sym` numbers by text**: for `T.Holds j a` and `T.Holds j' a'` with texts `t`, `t'` in `D`,
`j < j'` iff `t` is before `t'` in `Obj.lt` (the order of `asc`), whatever order the ids were inserted in. The
`2^63` bound of `ascDen_lt` is the number of texts of `D`: an ascending list of ranks maps to an ascending, so
repeat-free, list of texts of `D`. -/
theorem symAsc_lt_iff {D : Dict} {Rk : Tab .long .long} {P : Tab (.atom .sym) (.atom .sym)}
    {T : Tab .long (.atom .sym)} (h : symAsc D P = .ok T) (hR : rank D = .ok Rk) (wD : D.WF) (wP : Vals.WF P.key)
    (hb : D.n.toNat < 2 ^ 63) (hf : ∀ i t t', D.Holds i t → D.Holds i t' → t = t') {j j' : Int64} {a a' : UInt64}
    {t t' : (Obj.arr (.atom .char)).El} (hj : T.Holds j a) (hj' : T.Holds j' a') (ht : D.Holds a.toInt64 t)
    (ht' : D.Holds a'.toInt64 t') : j < j' ↔ Obj.lt (.arr (.atom .char)) t t' := by
  obtain ⟨-, r, hr, as⟩ := (symAsc_holds h hR wD wP j a).1 hj
  obtain ⟨-, r', hr', as'⟩ := (symAsc_holds h hR wD wP j' a').1 hj'
  have hbd : ∀ ys : List Obj.long.El, ys.Pairwise (Obj.lt .long) →
      (∀ b, b ∈ ys ↔ ∃ x, (∃ y, P.Holds x y) ∧ Rk.Holds x.toInt64 b) → ys.length < 2 ^ 63 := fun ys hys hm => by
    obtain ⟨zs, hl, hz, hq⟩ := rank_texts hR wD hb hf ys hys fun b hb' => by
      obtain ⟨x, -, hx⟩ := (hm b).1 hb'
      exact ⟨_, hx⟩
    have hnd : zs.Nodup := hz.imp fun {a b} hab e => by subst e; exact Obj.lt_irrefl _ a hab
    have hsub : zs ⊆ List.ofFn (fun j : Fin D.n.toNat => D.val.row j) := fun z hz' => by
      obtain ⟨-, -, -, -, j, -, hj⟩ := hq z hz'
      exact List.mem_ofFn.2 ⟨j, hj⟩
    have := nodup_length_le zs _ hnd hsub
    simp only [List.length_ofFn] at this
    omega
  exact (ascDen_lt hbd as as').trans ((Obj.lt_long r r').trans (rank_lt_iff hR wD hb hf ht ht' hr hr'))

end Rel.Lang.Table

namespace Rel.Lang

open Rel Rel.Rep Table

/-- `ran(R)` relates `x` to itself when `x` is a target of `R` (`Tm.ran_den`). -/
theorem Tm.ran_den' (ρ : Val) {A B : Obj} (R : Tm A B) (x v : Obj.El B) :
    (Tm.ran R).den ρ x v ↔ x = v ∧ ∃ m, R.den ρ m x := by
  rw [Tm.ran_den]
  simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip]
  constructor
  · rintro ⟨rfl, m, h, -⟩; exact ⟨rfl, m, h⟩
  · rintro ⟨rfl, m, h⟩; exact ⟨rfl, m, h, h⟩

/-- `dom(R)` relates `x` to itself when `x` is a source of `R` (`Tm.dom_den`). -/
theorem Tm.dom_den' (ρ : Val) {A B : Obj} (R : Tm A B) (x v : Obj.El A) :
    (Tm.dom R).den ρ x v ↔ x = v ∧ ∃ y, R.den ρ x y := by
  rw [Tm.dom_den]
  simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip]
  constructor
  · rintro ⟨rfl, m, h, -⟩; exact ⟨rfl, m, h⟩
  · rintro ⟨rfl, m, h⟩; exact ⟨rfl, m, h, h⟩

/-- **`<` on `sym` is the order of the texts**: with `r` the term `rank(D)` (`Elab.symOrd`), `r ≫ <(ran r) ≫ r°`
holds `(a, b)` when both ids have a rank and the text of `a` is before the text of `b` (`Obj.lt`, the order of `asc`),
whatever order the ids were inserted in. -/
theorem Tm.symLt_den (ρ : Val) (r : Tm (.atom .sym) (.atom .i64)) {D : Dict} {Rk : Tab .long .long}
    (h : rank D = .ok Rk) (wD : D.WF) (hb : D.n.toNat < 2 ^ 63)
    (hf : ∀ i t t', D.Holds i t → D.Holds i t' → t = t') (hr : ∀ a q, r.den ρ a q ↔ Rk.Holds a.toInt64 q)
    (a b : UInt64) :
    (Tm.comp r (.comp (.lt .i64 (.ran r)) (.conv r))).den ρ a b ↔
      (∃ q, Rk.Holds a.toInt64 q) ∧ (∃ s, Rk.Holds b.toInt64 s) ∧
        ∃ t u, D.Holds a.toInt64 t ∧ D.Holds b.toInt64 u ∧ Obj.lt (.arr (.atom .char)) t u := by
  simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, ltDen, ltAt, Tm.ran_den', hr]
  constructor
  · rintro ⟨x, hx, y, ⟨-, -, hxy⟩, hy⟩
    obtain ⟨t, ht, -⟩ := (rank_holds h wD _ _).1 hx
    obtain ⟨u, hu, -⟩ := (rank_holds h wD _ _).1 hy
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, t, u, ht, hu, (rank_lt_iff h wD hb hf ht hu hx hy).1 hxy⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, t, u, ht, hu, hlt⟩
    exact ⟨x, hx, y, ⟨⟨x, rfl, a, hx⟩, ⟨y, rfl, b, hy⟩, (rank_lt_iff h wD hb hf ht hu hx hy).2 hlt⟩, hy⟩

/-- **`asc` on `sym` numbers by text**: with `r` the term `rank(D)` and `Q = dom(S) r` for the set `S` (`Elab.symOrd`),
`asc(ran Q) ≫ Q°` is the table `symAsc D P` gives for `P` the relation `S` means, so `symAsc_lt_iff` orders it by text. -/
theorem Tm.symAsc_den (ρ : Val) (r : Tm (.atom .sym) (.atom .i64)) (S : Tm (.atom .sym) (.atom .sym)) {D : Dict}
    {Rk : Tab .long .long} {P : Tab (.atom .sym) (.atom .sym)} {T : Tab .long (.atom .sym)}
    (h : symAsc D P = .ok T) (hR : rank D = .ok Rk) (wD : D.WF) (wP : Vals.WF P.key)
    (hr : ∀ a q, r.den ρ a q ↔ Rk.Holds a.toInt64 q) (hS : ∀ a b, S.den ρ a b ↔ P.Holds a b) (j : Int64) (a : UInt64) :
    (Tm.comp (Tm.asc (.ran (.comp (.dom S) r))) (.conv (.comp (.dom S) r))).den ρ j a ↔ T.Holds j a := by
  rw [symAsc_holds h hR wD wP]
  have hset : (fun b => ∃ c, (Tm.ran (.comp (.dom S) r)).den ρ b c) =
      fun b => ∃ x, (∃ y, P.Holds x y) ∧ Rk.Holds x.toInt64 b := funext fun b => propext <| by
    simp only [Tm.ran_den', Tm.den, Core.Rel.comp, Tm.dom_den', hr, hS]
    constructor
    · rintro ⟨-, rfl, m, x, ⟨rfl, y, hy⟩, hx⟩; exact ⟨m, ⟨y, hy⟩, hx⟩
    · rintro ⟨x, ⟨y, hy⟩, hx⟩; exact ⟨b, rfl, x, x, ⟨rfl, y, hy⟩, hx⟩
  simp only [Tm.den, Tm.asc, Tm.argDen, Prim.den_ascRow, Core.Rel.comp, Core.Rel.recip, hset, Tm.dom_den', hr, hS]
  constructor
  · rintro ⟨q, hq, x, ⟨rfl, y, hy⟩, hx⟩; exact ⟨⟨y, hy⟩, q, hx, hq⟩
  · rintro ⟨⟨y, hy⟩, q, hx, hq⟩; exact ⟨q, hq, a, ⟨rfl, y, hy⟩, hx⟩

end Rel.Lang
