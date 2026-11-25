import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9326
abbrev V := Fin 21
def M := ([1179809,262467,524934,1049868,2585,5170,10340,20680,41360,82720,165440,330880,661760,1323520,549889,1099778,102405,204810,409620,819240,1638480] : List ℕ)
def E (i j : V) : ℕ := if (M.getD i.val 0).testBit j.val then 1 else 0
def f (a : Finset V) (j : V) := ∑ i ∈ a, E i j
private theorem deg : ∀ i : V, ∑ j : V, E i j = 5 := by decide +kernel
private theorem inner : ∀ i k : V, ∑ j : V, E i j * E k j = (if i = k then 5 else 1) := by decide +kernel
private theorem mass (a : Finset V) : ∑ j, f a j = 5 * a.card := by
  simp only [f]
  rw [Finset.sum_comm]
  simp [deg,Nat.mul_comm]
private theorem energy (a : Finset V) : ∑ j, (f a j)^2 = a.card * (a.card+4) := by
  have expand (j : V) : (f a j)^2 = ∑ i ∈ a, ∑ k ∈ a, E i j * E k j := by
    simp only [pow_two,f,Finset.sum_mul,Finset.mul_sum]
    exact Finset.sum_comm
  simp_rw [expand]
  rw [Finset.sum_comm]
  have single (i : V) (hi : i ∈ a) : (∑ j : V, ∑ k ∈ a, E i j * E k j) = a.card+4 := by
    rw [Finset.sum_comm]
    simp_rw [inner]
    have val (k : V) : (if i=k then 5 else 1 : ℕ) = 1+(if k=i then 4 else 0) := by
      by_cases e : i=k <;> simp_all [eq_comm]
    simp_rw [val]
    simp [Finset.sum_add_distrib,hi]
  calc
    _ = ∑ _i ∈ a, (a.card+4) := Finset.sum_congr rfl single
    _ = _ := by simp

theorem geometric (a b : Finset V) (zero : ∀ i ∈ a, ∀ j ∈ b, (M.getD i.val 0).testBit j.val = false) :
    25*a.card*a.card ≤ (21-b.card)*(a.card*(a.card+4)) ∧
     15*a.card ≤ a.card*(a.card+4)+2*(21-b.card) := by
  let g (j : V) : ℕ := if j ∈ b then 0 else 1
  have flat (j : V) : g j * f a j = f a j := by
    by_cases h : j ∈ b
    · have no : f a j = 0 := Finset.sum_eq_zero (fun i hi => by unfold E; rw [zero i hi j h]; rfl)
      simp [no]
    · simp [g,h]
  have g2 (j : V) : g j ^ 2 = (if j ∈ b then 0 else 1) := by by_cases h : j ∈ b <;> simp [g,h]
  have gs : ∑ j : V, g j ^ 2 = 21-b.card := by
    simp_rw [g2]
    have ind (j : V) : (if j ∈ b then 0 else 1 : ℕ) = (if j ∉ b then 1 else 0) := by by_cases h : j ∈ b <;> simp [h]
    simp_rw [ind]
    rw [Finset.sum_boole]
    have comp : Finset.univ.filter (fun x : V => x ∉ b) = bᶜ := by ext; simp
    rw [comp,Finset.card_compl]
    rfl
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset V) g (f a)
  simp_rw [flat] at h
  rw [gs,mass,energy] at h

  constructor
  · convert h using 1 <;> ring
  · have loc (j : V) : 3*f a j ≤ (f a j)^2 + 2*(g j)^2 := by
      by_cases hj : j ∈ b
      · have n : f a j = 0 := Finset.sum_eq_zero (fun i hi => by unfold E; rw [zero i hi j hj]; rfl)
        simp [n]
      · have v : g j = 1 := by simp [g,hj]
        rw [v]
        generalize f a j = n
        rcases n with _ | n
        · decide
        rcases n with _ | n
        · decide
        nlinarith [Nat.zero_le (n*n)]
    have z := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun j _ => loc j)
    simp only [← Finset.mul_sum,Finset.sum_add_distrib,mass,energy,gs] at z
    omega

def W (n : ℕ) := ([0,1,2,3,4,4,4,5,6,7,8,8,8,9,10,11,12] : List ℕ).getD (min 16 n) 12
private theorem wm : ∀ a b : Fin 17, a.val ≤ b.val → W a.val ≤ W b.val := by decide +kernel
private theorem ws : ∀ a b : Fin 17, W (a.val+b.val) ≤ W a.val + W b.val := by decide +kernel
theorem monotoneW : Monotone W := by
  intro a b h
  have v := wm ⟨min 16 a,by omega⟩ ⟨min 16 b,by omega⟩ (by simp; omega)
  simpa [W] using v
theorem subW (a b : ℕ) : W (a+b) ≤ W a + W b := by
  have v := ws ⟨min 16 a,by omega⟩ ⟨min 16 b,by omega⟩
  simp only [W] at v ⊢
  simpa only [show min 16 (min 16 a + min 16 b) = min 16 (a+b) by omega,
    show min 16 (min 16 a) = min 16 a by omega,show min 16 (min 16 b) = min 16 b by omega] using v
private theorem reversal : ∀ i j : V, (M.getD (-j).val 0).testBit (-i).val = (M.getD i.val 0).testBit j.val := by decide +kernel
def geom (a b : ℕ) := 25*a*a ≤ (21-b)*(a*(a+4)) ∧ 15*a ≤ a*(a+4)+2*(21-b)
private theorem numer : ∀ a b : Fin 22, geom a.val b.val → geom b.val a.val →
    a.val*W b.val + b.val*W a.val ≤ 48 := by unfold geom; decide +kernel
theorem weighted (a b : Finset V) (zero : ∀ i ∈ a, ∀ j ∈ b, (M.getD i.val 0).testBit j.val = false) :
    a.card*W b.card + b.card*W a.card ≤ 48 := by
  let neg : V ↪ V := ⟨fun x => -x, fun _ _ h => neg_injective h⟩
  have dual : ∀ i ∈ b.map neg, ∀ j ∈ a.map neg, (M.getD i.val 0).testBit j.val = false := by
    intro i hi j hj
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hj
    exact (reversal p l).trans (zero p hp l hl)
  have other := geometric _ _ dual
  simp only [Finset.card_map] at other
  have ha : a.card ≤ 21 := a.card_le_univ
  have hb : b.card ≤ 21 := b.card_le_univ
  exact numer ⟨a.card,by omega⟩ ⟨b.card,by omega⟩ (geometric a b zero) other
abbrev Box := Finset V × Finset V
private theorem wsum {α : Type} (S : Finset α) (f : α → ℕ) :
    W (∑ i ∈ S, f i) ≤ ∑ i ∈ S, W (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [W]
  | insert i s h ih =>
    rw [Finset.sum_insert h,Finset.sum_insert h]
    exact (subW _ _).trans (Nat.add_le_add_left ih _)
private theorem side (S : Finset Box) (A B : Box → Finset V)
    (Z : V → Finset V) (arity : ∀ i, (Z i).card = 16)
    (cov : ∀ i, ∀ j ∈ Z i, ∃ r ∈ S, i ∈ A r ∧ j ∈ B r) :
    252 ≤ ∑ r ∈ S, (A r).card*W (B r).card := by
  classical
  have row (i : V) : 12 ≤ ∑ r ∈ S, if i ∈ A r then W (B r).card else 0 := by
    let piece (r : Box) : Finset V := if i ∈ A r then B r else ∅
    have sub : Z i ⊆ S.biUnion piece := by
      intro j hj
      obtain ⟨r,hr,hin,jin⟩ := cov i j hj
      exact Finset.mem_biUnion.mpr ⟨r,hr,by simpa [piece,hin] using jin⟩
    have v := (Finset.card_le_card sub).trans Finset.card_biUnion_le
    rw [arity] at v
    have k := (monotoneW v).trans (wsum S (fun r => (piece r).card))
    have wk (r : Box) : W (piece r).card = (if i ∈ A r then W (B r).card else 0) := by
      by_cases h : i ∈ A r <;> simp [piece,h,W]
    simpa only [wk,show W 16 = 12 by decide] using k
  have k := Finset.sum_le_sum (s := (Finset.univ : Finset V)) (fun i _ => row i)
  rw [Finset.sum_comm] at k
  simpa using k
private def Z (i : V) : Finset V := Finset.univ.filter fun j => (M.getD i.val 0).testBit j.val = false
private def T (j : V) : Finset V := Finset.univ.filter fun i => (M.getD i.val 0).testBit j.val = false
private theorem zs : ∀ i : V, (Z i).card = 16 := by decide +kernel
private theorem ts : ∀ j : V, (T j).card = 16 := by decide +kernel
theorem eleven (L : List Box)
    (z : ∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (M.getD i.val 0).testBit j.val = false)
    (full : ∀ i j : V, (M.getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) :
    11 ≤ L.length := by
  let S := L.toFinset
  have a := side S Prod.fst Prod.snd Z zs (by
    intro i j h
    obtain ⟨r,hr,hi,hj⟩ := full i j (Finset.mem_filter.mp h).2
    exact ⟨r,List.mem_toFinset.mpr hr,hi,hj⟩)
  have b := side S Prod.snd Prod.fst T ts (by
    intro j i h
    obtain ⟨r,hr,hi,hj⟩ := full i j (Finset.mem_filter.mp h).2
    exact ⟨r,List.mem_toFinset.mpr hr,hj,hi⟩)
  have cost := Finset.sum_le_sum (s := S) (fun (r : Box) hr =>
    weighted r.1 r.2 (z r (List.mem_toFinset.mp hr)))
  rw [Finset.sum_add_distrib] at cost
  simp at cost
  have le : S.card ≤ L.length := List.toFinset_card_le _
  omega
end PEqualNP.Outside.L_meta_9326

theorem PEqualNP.Outside.L_meta_9326 : ¬ (∃ L : List (Finset (Fin 21) × Finset (Fin 21)), L.length ≤ 10 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 21) (j : Fin 21), (([1179809, 262467, 524934, 1049868, 2585, 5170, 10340, 20680, 41360, 82720, 165440, 330880, 661760, 1323520, 549889, 1099778, 102405, 204810, 409620, 819240, 1638480] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2) := by
  rintro ⟨L,h,z,hc⟩
  have lo := PEqualNP.Outside.L_meta_9326.eleven L z hc
  omega
