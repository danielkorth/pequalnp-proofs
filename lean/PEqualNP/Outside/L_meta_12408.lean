import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_12408

open PEqualNP.CircuitLowerBounds

abbrev Point := Fin 14
abbrev Mask := Finset Point

def target (b : Fin 4) : Mask := Finset.univ.filter fun p => Nat.testBit (p.val + 1) b.val

def initial : List Mask := List.ofFn fun p : Point => {p}

def read (w : List Mask) (i : ℕ) : Mask := w.getD i ∅

def join (w : List Mask) (g : Gate) : Mask :=
  read w (g.inputs.getD 0 w.length) ∪ read w (g.inputs.getD 1 w.length)

def trace (w : List Mask) : List Gate → List Mask
  | [] => []
  | g :: gs => join w g :: trace (w ++ [join w g]) gs

def allowed (g : Gate) : Prop := g.op = .or ∧ g.inputs.length ≤ 2

lemma in_read {w : List Mask} {i : ℕ} (h : read w i ≠ ∅) : read w i ∈ w := by
  unfold read at *
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi)] at h
    contradiction

lemma read_append_self (w : List Mask) : read w w.length = ∅ := by
  unfold read
  exact List.getD_eq_default _ _ (Nat.le_refl _)

lemma getD_map_mem (p : Point) (w : List Mask) (i : ℕ) :
    (w.map fun s => decide (p ∈ s)).getD i false = decide (p ∈ read w i) := by
  unfold read
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
        List.getD_eq_default _ _ (Nat.le_of_not_lt hi)]
    simp

lemma eval_join (p : Point) (w : List Mask) (g : Gate) (hg : allowed g) :
    g.op.eval (g.inputs.map fun i => (w.map fun s => decide (p ∈ s)).getD i false) =
      decide (p ∈ join w g) := by
  obtain ⟨ho, hn⟩ := hg
  rw [ho]
  obtain ⟨op, inputs⟩ := g
  cases inputs with
  | nil => simp [join, GateOp.eval, read_append_self]
  | cons a rest =>
    cases rest with
    | nil =>
      change (GateOp.or.eval [(w.map fun s => decide (p ∈ s)).getD a false]) =
        decide (p ∈ read w a ∪ read w w.length)
      simp [-List.getD_eq_getElem?_getD, GateOp.eval, read_append_self, getD_map_mem]
    | cons b rest =>
      cases rest with
      | nil =>
        change (GateOp.or.eval [(w.map fun s => decide (p ∈ s)).getD a false,
          (w.map fun s => decide (p ∈ s)).getD b false]) =
          decide (p ∈ read w a ∪ read w b)
        simp [-List.getD_eq_getElem?_getD, GateOp.eval, getD_map_mem]
      | cons c rest => simp at hn

lemma eval_trace (p : Point) (w : List Mask) (gs : List Gate) (hg : ∀ g ∈ gs, allowed g) :
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w.map fun s => decide (p ∈ s)) =
      (w ++ trace w gs).map (fun s => decide (p ∈ s)) := by
  induction gs generalizing w with
  | nil => simp [trace]
  | cons g gs ih =>
    simp only [List.foldl_cons, eval_join p w g (hg g (by simp))]
    rw [show (w.map fun s => decide (p ∈ s)) ++ [decide (p ∈ join w g)] =
      ((w ++ [join w g]).map fun s => decide (p ∈ s)) by simp]
    rw [ih _ (fun z hz => hg z (by simp [hz]))]
    simp [trace, List.append_assoc]

lemma initial_eval (p : Point) :
    initial.map (fun s => decide (p ∈ s)) = List.ofFn (fun q : Point => decide (q = p)) := by
  rw [initial, List.map_ofFn]
  simp [eq_comm]

lemma output_mask (C : Circuit) (hc : ∀ g ∈ C.gates, allowed g) (b : Fin 4) (i : ℕ)
    (hi : ∀ p : Point, (C.wires (List.ofFn (fun q : Point => decide (q = p)))).getD i false =
      Nat.testBit (p.val + 1) b.val) :
    read (initial ++ trace initial C.gates) i = target b := by
  ext p
  specialize hi p
  rw [Circuit.wires, ← initial_eval p, eval_trace p initial C.gates hc, getD_map_mem] at hi
  simp [target, ← hi]

lemma trace_length (w : List Mask) (gs : List Gate) : (trace w gs).length = gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

lemma initial_small {s : Mask} (h : s ∈ initial) : s.card ≤ 1 := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
  simp

lemma prior_pair (w : List Mask) (gs : List Gate)
    (hw : ∀ s ∈ w, 3 ≤ s.card → ∃ q ∈ w, q ⊂ s ∧ 2 ≤ q.card) :
    ∀ s ∈ w ++ trace w gs, 3 ≤ s.card →
      ∃ q ∈ w ++ trace w gs, q ⊂ s ∧ 2 ≤ q.card := by
  induction gs generalizing w with
  | nil => simpa [trace] using hw
  | cons g gs ih =>
    let a := read w (g.inputs.getD 0 w.length)
    let b := read w (g.inputs.getD 1 w.length)
    change ∀ s ∈ w ++ (a ∪ b) :: trace (w ++ [a ∪ b]) gs, 3 ≤ s.card →
      ∃ q ∈ w ++ (a ∪ b) :: trace (w ++ [a ∪ b]) gs, q ⊂ s ∧ 2 ≤ q.card
    rw [show w ++ (a ∪ b) :: trace (w ++ [a ∪ b]) gs =
        (w ++ [a ∪ b]) ++ trace (w ++ [a ∪ b]) gs by simp [List.append_assoc]]
    apply ih
    intro s hs hl
    have old : ∀ q ∈ w, q ∈ w ++ [a ∪ b] := fun q hq => List.mem_append_left _ hq
    rw [List.mem_append, List.mem_singleton] at hs
    rcases hs with hs | rfl
    · obtain ⟨q, hq, hh⟩ := hw s hs hl
      exact ⟨q, old q hq, hh⟩
    · have ha : a ⊆ a ∪ b := Finset.subset_union_left
      have hb : b ⊆ a ∪ b := Finset.subset_union_right
      have hq : ∃ q, (q = a ∨ q = b) ∧ q ⊆ a ∪ b ∧ 2 ≤ q.card := by
        by_cases hc : 2 ≤ a.card
        · exact ⟨a, Or.inl rfl, ha, hc⟩
        · exact ⟨b, Or.inr rfl, hb, by have := Finset.card_union_le a b; omega⟩
      obtain ⟨q, hq, hsub, hcard⟩ := hq
      have hne : q ≠ ∅ := by intro e; simp [e] at hcard
      have hmem : q ∈ w := by rcases hq with rfl | rfl <;> exact in_read hne
      by_cases he : q = a ∪ b
      · obtain ⟨r, hr, hh⟩ := hw q hmem (he ▸ hl)
        exact ⟨r, old r hr, he ▸ hh⟩
      · exact ⟨q, old q hmem, Finset.ssubset_iff_subset_ne.mpr ⟨hsub, he⟩, hcard⟩

def groupA (i : Fin 6) : Fin 4 := (![0, 0, 0, 1, 1, 2] : Fin 6 → Fin 4) i

def groupB (i : Fin 6) : Fin 4 := (![1, 2, 3, 2, 3, 3] : Fin 6 → Fin 4) i

def group (i : Fin 6) : Mask := target (groupA i) ∩ target (groupB i)

lemma group_distinct (i : Fin 6) : groupA i ≠ groupB i := by decide +kernel +revert

lemma pair_group (b c : Fin 4) (h : b ≠ c) :
    ∃ i, (b = groupA i ∧ c = groupB i) ∨ (b = groupB i ∧ c = groupA i) := by
  revert b c
  decide +kernel

lemma distinct_groups (i j : Fin 6) (h : i ≠ j) : (group i ∩ group j).card ≤ 1 := by
  revert i j
  decide +kernel

def shared (i : Fin 6) (s : Mask) : Bool := decide (2 ≤ s.card ∧ s ⊆ group i)

def exclusive (b : Fin 4) (s : Mask) : Bool :=
  decide (2 ≤ s.card ∧ s ⊆ target b ∧ ∀ c : Fin 4, c ≠ b → ¬ s ⊆ target c)

-- Track which marked inputs have been joined along wires contained in one output.
-- Each gate exclusive to that output can merge at most two classes.
def markedTogether (m s : Mask) (f : Point → Point) : Prop :=
  ∀ a ∈ m ∩ s, ∀ b ∈ m ∩ s, f a = f b

def consistent (t m : Mask) (w : List Mask) (f : Point → Point) : Prop :=
  ∀ s ∈ w, s ⊆ t → markedTogether m s f

lemma together_small {m s : Mask} {f : Point → Point} (h : (m ∩ s).card ≤ 1) :
    markedTogether m s f := by
  intro a ha b hb
  rw [Finset.card_le_one] at h
  rw [h a ha b hb]

lemma together_union (m a b : Mask) (f : Point → Point)
    (ha : markedTogether m a f) (hb : markedTogether m b f) :
    ∃ k : Point → Point, (∀ x y, f x = f y → k x = k y) ∧
      markedTogether m (a ∪ b) k ∧ (m.image f).card ≤ (m.image k).card + 1 := by
  by_cases ea : (m ∩ a).Nonempty
  · by_cases eb : (m ∩ b).Nonempty
    · obtain ⟨x, hx⟩ := ea
      obtain ⟨y, hy⟩ := eb
      let k := fun p => if f p = f y then f x else f p
      have hk : ∀ p q, f p = f q → k p = k q := by
        intro p q h
        simp [k, h]
      have kxy : k x = k y := by
        simp only [k, ite_true, eq_self]
        split <;> simp_all
      have contain : m.image f ⊆ insert (f y) (m.image k) := by
        intro j hj
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hj
        by_cases e : f p = f y
        · simp [e]
        · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, by simp [k, e]⟩)
      refine ⟨k, hk, ?_, (Finset.card_le_card contain).trans (Finset.card_insert_le (f y) (m.image k))⟩
      have allx : ∀ p ∈ m ∩ (a ∪ b), k p = k x := by
        intro p hp
        simp only [Finset.mem_inter, Finset.mem_union] at hp
        rcases hp.2 with h | h
        · exact hk _ _ (ha p (Finset.mem_inter.mpr ⟨hp.1, h⟩) x hx)
        · exact (hk _ _ (hb p (Finset.mem_inter.mpr ⟨hp.1, h⟩) y hy)).trans kxy.symm
      exact fun p hp q hq => (allx p hp).trans (allx q hq).symm
    · have e : m ∩ (a ∪ b) = m ∩ a := by
        rw [Finset.inter_union_distrib_left, Finset.not_nonempty_iff_eq_empty.mp eb, Finset.union_empty]
      exact ⟨f, fun _ _ h => h, fun p hp q hq => ha p (e ▸ hp) q (e ▸ hq), Nat.le_succ _⟩
  · have e : m ∩ (a ∪ b) = m ∩ b := by
      rw [Finset.inter_union_distrib_left, Finset.not_nonempty_iff_eq_empty.mp ea, Finset.empty_union]
    exact ⟨f, fun _ _ h => h, fun p hp q hq => hb p (e ▸ hp) q (e ▸ hq), Nat.le_succ _⟩

lemma together_read {t m : Mask} {w : List Mask} {f : Point → Point} (h : consistent t m w f)
    (i : ℕ) (hi : read w i ⊆ t) : markedTogether m (read w i) f := by
  by_cases e : read w i = ∅
  · simp [e, markedTogether]
  · exact h _ (in_read e) hi

lemma count_marks (b : Fin 4) (m : Mask) (w : List Mask) (gs : List Gate)
    (hs : ∀ s ∈ trace w gs, s ⊆ target b → exclusive b s = false → (m ∩ s).card ≤ 1)
    (f : Point → Point) (hc : consistent (target b) m w f) :
    ∃ k, consistent (target b) m (w ++ trace w gs) k ∧
      (m.image f).card ≤ (m.image k).card + (trace w gs).countP (exclusive b) := by
  induction gs generalizing w f with
  | nil => exact ⟨f, by simpa [trace] using hc, by simp [trace]⟩
  | cons g gs ih =>
    let s := join w g
    have hsmall : s ⊆ target b → exclusive b s = false → (m ∩ s).card ≤ 1 :=
      hs s (by simp [trace, s])
    have finish (k : Point → Point) (hold : ∀ x y, f x = f y → k x = k y)
        (hnew : s ⊆ target b → markedTogether m s k)
        (hcst : (m.image f).card ≤ (m.image k).card + (exclusive b s).toNat) :
        ∃ l, consistent (target b) m (w ++ trace w (g :: gs)) l ∧
          (m.image f).card ≤ (m.image l).card + (trace w (g :: gs)).countP (exclusive b) := by
      have valid : consistent (target b) m (w ++ [s]) k := by
        intro z hz ht
        rw [List.mem_append, List.mem_singleton] at hz
        rcases hz with hz | rfl
        · exact fun x hx y hy => hold _ _ (hc z hz ht x hx y hy)
        · exact hnew ht
      obtain ⟨l, hl, hn⟩ := ih (w ++ [s]) (fun z hz => hs z (by simp [trace, s, hz])) k valid
      refine ⟨l, by simpa [trace, s, List.append_assoc] using hl, ?_⟩
      rw [show trace w (g :: gs) = s :: trace (w ++ [s]) gs by rfl, List.countP_cons]
      cases e : exclusive b s <;> simp [e] at hcst ⊢ <;> omega
    by_cases ht : s ⊆ target b
    · cases he : exclusive b s with
      | false =>
        exact finish f (fun _ _ h => h) (fun _ => together_small (hsmall ht he)) (by simp [he])
      | true =>
        have ha : read w (g.inputs.getD 0 w.length) ⊆ target b :=
          Finset.subset_union_left.trans ht
        have hb : read w (g.inputs.getD 1 w.length) ⊆ target b :=
          Finset.subset_union_right.trans ht
        obtain ⟨k, hk, hnew, hkcost⟩ := together_union m _ _ f
          (together_read hc _ ha) (together_read hc _ hb)
        exact finish k hk (fun _ => hnew) (by simpa [he] using hkcost)
    · exact finish f (fun _ _ h => h) (fun h => (ht h).elim) (Nat.le_add_right _ _)

def bits (n : ℕ) : Mask := Finset.univ.filter fun p => n.testBit p.val

def option (i : Fin 6) (a : Fin 5) : Mask := bits ((![
  ![0, 68, 1028, 1088, 1092],
  ![0, 80, 4112, 4160, 4176],
  ![0, 1280, 4352, 5120, 5376],
  ![0, 96, 8224, 8256, 8288],
  ![0, 1536, 8704, 9216, 9728],
  ![0, 6144, 10240, 12288, 14336]] : Fin 6 → Fin 5 → ℕ) i a)

def cost (a : Fin 5) : ℕ := if a = 0 then 0 else if a = 4 then 2 else 1

-- Each record packs a 14-bit marker mask followed by its three-bit cardinality.
-- The record index selects the three overlap options incident to the output.
def packData (b : Fin 4) : ℕ := (![
  2452143384175150469137506442908554575759139957725276115143230705408933563691692555273972027029514003143217238949358610672614397623209534303309395913422364221113209015780241503487376072087973940031717066303080441059053507382413612950559054659129546808807447549356248722647804172892291301580184868341257123288869665928995047898227821176228985760344681331815234435135386885028457718493436804189630801264854917709393375487449786163442260054558378320786737090986250476430072497352776594151444348283928727426544048617092761679398276552470555971429232353809221813085338440934744968094122537385651248257121457797901249988206149230921587706942969173,
  2462315160934754439144564915534266443119009775899435746135633787308400483609008054330703363590030852930617278741023835463933419772438522299108443088744613606363959048075073953153767296069916673136518465106235873104626887861309039775694705626079860365935666419161237540115756164020005541288724013423160794964720089277152690647553520268277107043180950819596826935020208023792423497463262801060682099650560199412393531020315520859770618099780389316432372226909908280230668373340022661861261505169334395858272871850639328541878190046046347818224047177201098612122089355461980409941635151641388041009194230159495604678244399357634795255664338534,
  2520216044027884729953974682788147286610561336957837228728136402903091161212957731639928631168988288972642807541701350427263452850376688578429601304352858682357825058438106259703779694715739265135426051672830700733800942935708123049205490275939923648822443629869863012490762132166110379710178861630870994802950474614980340105626644356547368295801766527033717320807655338468453770626433280168941617764491011825862354004597826577660826101745740930643658926221344689649608570507386805930012838042354971022865696182413151812847871953530194422922841784143172101060630831012932935858451113670948378929221551275418268594104304072393114204020799608,
  2551513818672820022283385367790245039849237856448865057156516195116437473431308908563834181211667984130494444731256763920955362622235151389666709627645085640521306325613647948790549791889948234862945608853575863147704533872536462758060710685702005070517878648766750375095764313184465370522255427504710747831586417691973528144778841804930039640101714067894103824065126488555862071140473151189337621691443942810544133394224611999276717149288876783790631105504173162134433613420574249471561626536614254903820697105994380610796987121896211855628763981076120894646885372567795058609247990920609411090613947126608928071525071332171247450067173248] : Fin 4 → ℕ) b

def firstGroup (b : Fin 4) : Fin 6 := (![0, 0, 1, 2] : Fin 4 → Fin 6) b

def middleGroup (b : Fin 4) : Fin 6 := (![1, 3, 3, 4] : Fin 4 → Fin 6) b

def lastGroup (b : Fin 4) : Fin 6 := (![2, 4, 5, 5] : Fin 4 → Fin 6) b

def packEntry (b : Fin 4) (x y z : Fin 5) : ℕ × ℕ :=
  let n := (packData b / (2 ^ (17 * (25 * x.val + 5 * y.val + z.val)))) % 131072
  (n % 16384, n / 16384)

def entry (b : Fin 4) (profile : Fin 6 → Fin 5) : ℕ × ℕ :=
  packEntry b (profile (firstGroup b)) (profile (middleGroup b)) (profile (lastGroup b))

def usesGroup (b : Fin 4) (i : Fin 6) : Prop := b = groupA i ∨ b = groupB i

lemma uses_group_indices : ∀ (b : Fin 4) (i : Fin 6),
    usesGroup b i → i = firstGroup b ∨ i = middleGroup b ∨ i = lastGroup b := by
  unfold usesGroup
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma packEntry_valid : ∀ (b : Fin 4) (x y z : Fin 5),
    let m := bits (packEntry b x y z).1
    m ⊆ target b ∧ m.card = (packEntry b x y z).2 ∧
      (m ∩ option (firstGroup b) x).card ≤ 1 ∧
      (m ∩ option (middleGroup b) y).card ≤ 1 ∧
      (m ∩ option (lastGroup b) z).card ≤ 1 := by
  intro b x y
  fin_cases b <;> fin_cases x <;> fin_cases y <;> decide +kernel

lemma packing (profile : Fin 6 → Fin 5) (b : Fin 4) :
    let m := bits (entry b profile).1
    m ⊆ target b ∧ m.card = (entry b profile).2 ∧
      ∀ i, usesGroup b i → (m ∩ option i (profile i)).card ≤ 1 := by
  obtain ⟨hs, hc, h1, h2, h3⟩ := packEntry_valid b (profile (firstGroup b))
    (profile (middleGroup b)) (profile (lastGroup b))
  refine ⟨hs, hc, ?_⟩
  intro i hi
  rcases uses_group_indices b i hi with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

def six (a b c d e f : Fin 5) : Fin 6 → Fin 5 := ![a, b, c, d, e, f]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma finite_budget : ∀ a b c d e f : Fin 5,
    24 ≤ (∑ i : Fin 6, cost (six a b c d e f i)) +
      ∑ v : Fin 4, (entry v (six a b c d e f)).2 := by
  intro a b c d
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Finset.sum_empty, add_zero]
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

lemma packed_budget (profile : Fin 6 → Fin 5) :
    24 ≤ (∑ i : Fin 6, cost (profile i)) + ∑ b : Fin 4, (entry b profile).2 := by
  have h : profile = six (profile 0) (profile 1) (profile 2) (profile 3) (profile 4) (profile 5) := by
    funext i
    fin_cases i <;> rfl
  rw [h]
  exact finite_budget _ _ _ _ _ _

lemma option_zero (i : Fin 6) : option i 0 = ∅ := by decide +kernel +revert

lemma option_four (i : Fin 6) : option i 4 = group i := by decide +kernel +revert

set_option maxRecDepth 10000 in
lemma pair_option_check : ∀ (i : Fin 6) (p q : Point),
    p ∈ group i → q ∈ group i → p ≠ q →
    ∃ a : Fin 5, cost a = 1 ∧ ({p, q} : Mask) = option i a := by
  intro i
  fin_cases i <;> decide +kernel

lemma pair_option (i : Fin 6) (s : Mask) (hs : s ⊆ group i) (hc : s.card = 2) :
    ∃ a : Fin 5, cost a = 1 ∧ s = option i a := by
  obtain ⟨p, q, hn, rfl⟩ := Finset.card_eq_two.mp hc
  exact pair_option_check i p q (hs (by simp)) (hs (by simp)) hn

lemma shared_spec {i : Fin 6} {s : Mask} (h : shared i s = true) : 2 ≤ s.card ∧ s ⊆ group i := by
  exact of_decide_eq_true h

-- A group with one shared gate can supply only a pair. A triple needs an
-- earlier gate with a proper two-element support in the same group.
lemma profile_one (gs : List Gate) (i : Fin 6) :
    ∃ a : Fin 5, cost a ≤ (trace initial gs).countP (shared i) ∧
      ∀ s ∈ trace initial gs, shared i s = true → s ⊆ option i a := by
  let selected := (trace initial gs).filter (shared i)
  have count : (trace initial gs).countP (shared i) = selected.length := by
    rw [List.countP_eq_length_filter]
  have memMatches {s : Mask} :
      s ∈ selected ↔ s ∈ trace initial gs ∧ shared i s = true := List.mem_filter
  by_cases hmany : 2 ≤ selected.length
  · refine ⟨4, by simpa [cost, count] using hmany, ?_⟩
    intro s _ hs
    rw [option_four]
    exact (shared_spec hs).2
  · cases e : selected with
    | nil =>
      refine ⟨0, by simp [cost], ?_⟩
      intro s hs h
      have := memMatches.mpr ⟨hs, h⟩
      simp [e] at this
    | cons s rest =>
      have emp : rest = [] := by
        have hlen : rest.length = 0 := by
          rw [e, List.length_cons] at hmany
          omega
        exact List.length_eq_zero_iff.mp hlen
      subst rest
      rw [e] at count
      have hs : s ∈ trace initial gs ∧ shared i s = true := memMatches.mp (by simp [e])
      obtain ⟨hcard, hsub⟩ := shared_spec hs.2
      have exactly : s.card = 2 := by
        by_contra h
        have has : 3 ≤ s.card := by omega
        obtain ⟨q, hq, hstrict, hqcard⟩ := prior_pair initial gs
          (fun r hr h => (by have := initial_small hr; omega))
          s (List.mem_append_right _ hs.1) has
        rw [List.mem_append] at hq
        have qt : q ∈ trace initial gs := by
          rcases hq with hp | hp
          · have := initial_small hp
            omega
          · exact hp
        have hshared : shared i q = true := decide_eq_true ⟨hqcard, hstrict.le.trans hsub⟩
        have qm := memMatches.mpr ⟨qt, hshared⟩
        rw [e, List.mem_singleton] at qm
        exact (ne_of_lt hstrict) qm
      obtain ⟨a, ha, eq⟩ := pair_option i s hsub exactly
      refine ⟨a, by simp [ha, count], ?_⟩
      intro q hq h
      have qm := memMatches.mpr ⟨hq, h⟩
      rw [e, List.mem_singleton] at qm
      simp [qm, ← eq]

lemma excluded_small (gs : List Gate) (profile : Fin 6 → Fin 5)
    (hp : ∀ i, ∀ s ∈ trace initial gs, shared i s = true → s ⊆ option i (profile i))
    (b : Fin 4) (s : Mask) (hs : s ∈ trace initial gs) (ht : s ⊆ target b)
    (he : exclusive b s = false) :
    (bits (entry b profile).1 ∩ s).card ≤ 1 := by
  by_cases hcard : 2 ≤ s.card
  · classical
    have existsOther : ∃ c : Fin 4, c ≠ b ∧ s ⊆ target c := by
      have hh : ¬ ∀ c : Fin 4, c ≠ b → ¬ s ⊆ target c := by
        intro h
        have he' : exclusive b s = true := decide_eq_true ⟨hcard, ht, h⟩
        rw [he] at he'
        contradiction
      push Not at hh
      exact hh
    obtain ⟨c, hn, hc⟩ := existsOther
    obtain ⟨i, hi⟩ := pair_group b c hn.symm
    have huse : usesGroup b i := hi.imp And.left And.left
    have hsub : s ⊆ group i := by
      unfold group
      rcases hi with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · exact Finset.subset_inter (ha ▸ ht) (hb ▸ hc)
      · exact Finset.subset_inter (hb ▸ hc) (ha ▸ ht)
    have hoption := hp i s hs (show shared i s = true from decide_eq_true ⟨hcard, hsub⟩)
    exact (Finset.card_le_card (Finset.inter_subset_inter (fun _ h => h) hoption)).trans
      ((packing profile b).2.2 i huse)
  · have h := Finset.card_le_card (Finset.inter_subset_right (s₁ := bits (entry b profile).1) (s₂ := s))
    omega

lemma exclusive_output (C : Circuit) (hc : ∀ g ∈ C.gates, allowed g) (profile : Fin 6 → Fin 5)
    (hp : ∀ i, ∀ s ∈ trace initial C.gates, shared i s = true → s ⊆ option i (profile i))
    (b : Fin 4) (i : ℕ)
    (hi : ∀ p : Point, (C.wires (List.ofFn (fun q : Point => decide (q = p)))).getD i false =
      Nat.testBit (p.val + 1) b.val) :
    (entry b profile).2 ≤ 1 + (trace initial C.gates).countP (exclusive b) := by
  let m := bits (entry b profile).1
  have hstart : consistent (target b) m initial id := by
    intro s hs _
    exact together_small ((Finset.card_le_card Finset.inter_subset_right).trans (initial_small hs))
  obtain ⟨k, hk, hcount⟩ := count_marks b m initial C.gates
    (fun s hs ht he => excluded_small C.gates profile hp b s hs ht he) id hstart
  have houtput := output_mask C hc b i hi
  have hsmall : (m.image k).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha d hd
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hd
    have hne : target b ≠ ∅ := by
      intro e
      have : m ⊆ ∅ := e ▸ (packing profile b).1
      exact (Finset.notMem_empty p) (this hp)
    have hin : target b ∈ initial ++ trace initial C.gates := by
      rw [← houtput]
      exact in_read (houtput.symm ▸ hne)
    have aux {p : Point} (hh : p ∈ m) : p ∈ m ∩ target b :=
      Finset.mem_inter.mpr ⟨hh, (packing profile b).1 hh⟩
    exact hk _ hin (fun _ h => h) p (aux hp) q (aux hq)
  rw [Finset.image_id, (packing profile b).2.1] at hcount
  omega

abbrev Charge := Fin 6 ⊕ Fin 4

def charged : Charge → Mask → Bool
  | .inl i => shared i
  | .inr b => exclusive b

lemma at_most_one_charge (s : Mask) (a b : Charge)
    (ha : charged a s = true) (hb : charged b s = true) : a = b := by
  have mixed {i : Fin 6} {v : Fin 4} (h : shared i s = true) (e : exclusive v s = true) : False := by
    have hs := (shared_spec h).2
    have hspec : 2 ≤ s.card ∧ s ⊆ target v ∧ ∀ c : Fin 4, c ≠ v → ¬ s ⊆ target c :=
      of_decide_eq_true e
    have ha : s ⊆ target (groupA i) := hs.trans Finset.inter_subset_left
    have hb : s ⊆ target (groupB i) := hs.trans Finset.inter_subset_right
    by_cases eq : groupA i = v
    · exact hspec.2.2 (groupB i) (by rw [← eq]; exact (group_distinct i).symm) hb
    · exact hspec.2.2 (groupA i) eq ha
  rcases a with a | a <;> rcases b with b | b
  · congr 1
    by_contra e
    have h := Finset.card_le_card (Finset.subset_inter (shared_spec ha).2 (shared_spec hb).2)
    have hc := (shared_spec ha).1
    have hd := distinct_groups a b e
    omega
  · exact (mixed ha hb).elim
  · exact (mixed hb ha).elim
  · congr 1
    by_contra e
    have hA : 2 ≤ s.card ∧ s ⊆ target a ∧ ∀ c : Fin 4, c ≠ a → ¬ s ⊆ target c :=
      of_decide_eq_true ha
    have hB : 2 ≤ s.card ∧ s ⊆ target b ∧ ∀ c : Fin 4, c ≠ b → ¬ s ⊆ target c :=
      of_decide_eq_true hb
    exact hA.2.2 b (Ne.symm e) hB.2.1

lemma charges_count (ss : List Mask) : (∑ a : Charge, ss.countP (charged a)) ≤ ss.length := by
  classical
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.countP_cons, Finset.sum_add_distrib, List.length_cons]
    have one : (∑ a : Charge, if charged a s then (1 : ℕ) else 0) ≤ 1 := by
      by_cases h : ∃ a : Charge, charged a s = true
      · obtain ⟨a, ha⟩ := h
        rw [Finset.sum_eq_single a]
        · simp [ha]
        · intro b _ hne
          cases hb : charged b s with
          | false => simp
          | true => exact (hne (at_most_one_charge s b a hb ha)).elim
        · simp
      · push Not at h
        have allFalse (a : Charge) : charged a s = false := Bool.eq_false_of_ne_true (h a)
        simp [allFalse]
    omega

lemma budget_counts (ss : List Mask) :
    (∑ i : Fin 6, ss.countP (shared i)) + ∑ b : Fin 4, ss.countP (exclusive b) ≤ ss.length := by
  have h := charges_count ss
  rw [Fintype.sum_sum_type] at h
  exact h

lemma encoder_bound (C : Circuit) (hc : ∀ g ∈ C.gates, allowed g)
    (outputs : ∀ b : Fin 4, ∃ i : ℕ, ∀ p : Point,
      (C.wires (List.ofFn (fun q : Point => decide (q = p)))).getD i false =
      Nat.testBit (p.val + 1) b.val) :
    20 ≤ C.size := by
  classical
  choose profile hcost hgroup using profile_one C.gates
  have covered (b : Fin 4) : (entry b profile).2 ≤ 1 + (trace initial C.gates).countP (exclusive b) := by
    obtain ⟨i, hi⟩ := outputs b
    exact exclusive_output C hc profile hgroup b i hi
  have hexcl := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => covered b)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hexcl
  have hshared := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hcost i)
  have hlimit := budget_counts (trace initial C.gates)
  have hp := packed_budget profile
  rw [trace_length] at hlimit
  unfold Circuit.size
  omega

end PEqualNP.Outside.L_meta_12408

theorem PEqualNP.Outside.L_meta_12408 : ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ g.inputs.length ≤ 2) ∧ C.size ≤ 19 ∧ ∀ v : Fin 4, ∃ w : ℕ, ∀ p : Fin 14, (C.wires (List.ofFn (fun q : Fin 14 => decide (q = p)))).getD w false = Nat.testBit (p.val + 1) v.val) := by
  rintro ⟨C, hc, hsize, ho⟩
  have := PEqualNP.Outside.L_meta_12408.encoder_bound C hc ho
  omega
