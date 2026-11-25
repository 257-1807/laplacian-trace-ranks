module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Turan
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

public section

namespace TraceRanks

open SimpleGraph Finset Matrix

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]

/-- An induced clique supplies a principal submatrix of the adjacency matrix. -/
private theorem clique_rank_le {k : ℕ} (f : completeGraph (Fin k) ↪g G) :
    ((completeGraph (Fin k)).adjMatrix ℝ).rank ≤ (G.adjMatrix ℝ).rank := by
  have h : (G.adjMatrix ℝ).submatrix f f = (completeGraph (Fin k)).adjMatrix ℝ := by
    ext u v
    simp [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
  rw [← h]
  exact Matrix.rank_submatrix_le _ _ _

private theorem edge_rank : ((completeGraph (Fin 2)).adjMatrix ℝ).rank = 2 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  norm_num [Matrix.det_fin_two, SimpleGraph.adjMatrix_apply, SimpleGraph.top_adj]

private theorem triangle_rank : ((completeGraph (Fin 3)).adjMatrix ℝ).rank = 3 := by
  apply Matrix.rank_of_isUnit
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  norm_num [Matrix.det_fin_three, SimpleGraph.adjMatrix_apply, SimpleGraph.top_adj]

private theorem rank_ge_two (hn : 2 ≤ n) (hc : G.Connected) : 2 ≤ (G.adjMatrix ℝ).rank := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h : ¬ G.CliqueFree 2 := by
    rw [SimpleGraph.cliqueFree_two]
    intro he
    rw [he, connected_bot_iff] at hc
    exact (not_subsingleton (Fin n)) hc.1
  simpa only [edge_rank] using clique_rank_le G (G.topEmbeddingOfNotCliqueFree h)

private theorem triangle_free_of_rank_le_two (h : (G.adjMatrix ℝ).rank ≤ 2) : G.CliqueFree 3 := by
  by_contra htri
  have := clique_rank_le G (G.topEmbeddingOfNotCliqueFree htri)
  rw [triangle_rank] at this
  omega

/-- Rank-nullity for the graph Laplacian in the connected case. -/
theorem lap_rank (hc : G.Connected) : (G.lapMatrix ℝ).rank = n-1 := by
  classical
  have hcomp : Fintype.card G.ConnectedComponent = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact SimpleGraph.card_connectedComponent_eq_one_iff.mpr hc
  have h := LinearMap.finrank_range_add_finrank_ker (G.lapMatrix ℝ).toLin'
  rw [← G.card_connectedComponent_eq_finrank_ker_toLin'_lapMatrix, hcomp, Module.finrank_pi,
    Fintype.card_fin, Matrix.toLin'_apply'] at h
  change Module.finrank ℝ (LinearMap.range (G.lapMatrix ℝ).mulVecLin) = n-1
  omega

theorem lap_trace : (G.lapMatrix ℝ).trace = (2 * G.edgeFinset.card : ℕ) := by
  rw [← G.sum_degrees_eq_twice_card_edges, Nat.cast_sum]
  simp [SimpleGraph.lapMatrix, Matrix.trace_sub, SimpleGraph.trace_adjMatrix,
    SimpleGraph.degMatrix, Matrix.trace_diagonal]

private theorem order_bound (k : ℕ) : (k+6)*(k+5) < 2^(k+5) := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k+1+5 = k+5+1 by omega, pow_succ]
    nlinarith

private theorem arithmetic (n r e : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r)
    (hd : e ≤ n.choose 2) (ht : r ≤ 2 → e ≤ n^2/4) :
    2*e ≤ r * 2^(n-2) := by
  by_cases hlarge : 6 ≤ n
  · obtain ⟨k, hk⟩ : ∃ k, n = k + 6 := ⟨n-6, by omega⟩
    subst n
    rw [Nat.choose_two_right] at hd
    have hquad := order_bound k
    have hdiff : k+6-1 = k+5 := by omega
    rw [hdiff] at hd
    calc
      2*e ≤ (k+6)*(k+5) := by omega
      _ ≤ 2^(k+5) := hquad.le
      _ = 2 * 2^(k+6-2) := by rw [show k+5 = (k+6-2)+1 by omega, pow_succ, Nat.mul_comm]
      _ ≤ _ := Nat.mul_le_mul_right _ hr
  · rw [Nat.choose_two_right] at hd
    by_cases h2 : r ≤ 2
    · have hm := ht h2
      interval_cases n <;> norm_num at * <;> omega
    · interval_cases n <;> norm_num at * <;> omega

/-- A linear dependence on adjacency rank suffices once the exponential base is fixed at two. -/
theorem stronger (hn : 2 ≤ n) (hc : G.Connected) :
    2*G.edgeFinset.card ≤ (G.adjMatrix ℝ).rank * 2^(n-2) := by
  apply arithmetic n _ _ hn (rank_ge_two G hn hc)
  · simpa using G.card_edgeFinset_le_card_choose_two
  · intro h
    have ht := (triangle_free_of_rank_le_two G h).card_edgeFinset_le (r := 2)
    simpa only [Fintype.card_fin, SimpleGraph.turanNumber_two] using ht

/-- Duhamel–Cazenave corpus conjecture 124806, with both actual real matrix ranks. -/
theorem conjecture_124806 (hn : 2 ≤ n) (hc : G.Connected) :
    (G.lapMatrix ℝ).trace ≤ ((G.adjMatrix ℝ).rank : ℝ) ^ (G.lapMatrix ℝ).rank := by
  rw [lap_trace, lap_rank G hc]
  have h := stronger G hn hc
  have hr := rank_ge_two G hn hc
  have hpow := Nat.pow_le_pow_left hr (n-2)
  have hb : 2*G.edgeFinset.card ≤ (G.adjMatrix ℝ).rank ^ (n-1) := by
    rw [show n-1 = (n-2)+1 by omega, pow_succ']
    exact h.trans (Nat.mul_le_mul_left _ hpow)
  exact_mod_cast hb

private theorem ext_parameters (n r e : ℕ) (hn : 2 ≤ n) (hr : 2 ≤ r)
    (hd : e ≤ n.choose 2) (ht : r ≤ 2 → e ≤ n^2/4) (eqn : 2*e = r^(n-1)) :
    n ≤ 4 ∧ r = 2 ∧ e = n^2/4 := by
  rw [Nat.choose_two_right] at hd
  have hsmall : n < 6 := by
    by_contra! hl
    obtain ⟨k, hk⟩ : ∃ k, n = k+6 := ⟨n-6, by omega⟩
    subst n
    have h := order_bound k
    have hp := Nat.pow_le_pow_left hr (k+5)
    have hdiff : k+6-1 = k+5 := by omega
    rw [hdiff] at hd eqn
    omega
  have heq : r = 2 := by
    by_contra hne
    have hr3 : 3 ≤ r := by omega
    have hp := Nat.pow_le_pow_left hr3 (n-1)
    interval_cases n <;> norm_num at * <;> omega
  subst r
  have hm := ht le_rfl
  interval_cases n <;> norm_num at * <;> omega

private theorem turan_rank_le_two (k : ℕ) : ((turanGraph k 2).adjMatrix ℝ).rank ≤ 2 := by
  let c (v : Fin k) : Fin 2 := ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩
  have h : ((completeGraph (Fin 2)).adjMatrix ℝ).submatrix c c = (turanGraph k 2).adjMatrix ℝ := by
    ext i j
    simp [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply, turanGraph_adj, c, Fin.ext_iff]
  rw [← h]
  exact (Matrix.rank_submatrix_le _ _ _).trans_eq edge_rank

/-- Equality holds precisely on the balanced complete bipartite graphs of orders 2, 3, and 4. -/
theorem equality_iff (hn : 2 ≤ n) (hc : G.Connected) :
    (G.lapMatrix ℝ).trace = ((G.adjMatrix ℝ).rank : ℝ) ^ (G.lapMatrix ℝ).rank ↔
      n ≤ 4 ∧ Nonempty (G ≃g turanGraph n 2) := by
  rw [lap_trace, lap_rank G hc]
  constructor
  · intro heq
    have eqn : 2 * G.edgeFinset.card = (G.adjMatrix ℝ).rank ^ (n-1) := by exact_mod_cast heq
    have ht (h : (G.adjMatrix ℝ).rank ≤ 2) : G.edgeFinset.card ≤ n^2/4 := by
      simpa only [Fintype.card_fin, turanNumber_two] using
        (triangle_free_of_rank_le_two G h).card_edgeFinset_le (r := 2)
    obtain ⟨hn4, hr, he⟩ := ext_parameters n _ _ hn (rank_ge_two G hn hc)
      (by simpa using G.card_edgeFinset_le_card_choose_two) ht eqn
    refine ⟨hn4, ?_⟩
    have hmax : G.IsTuranMaximal 2 := by
      refine ⟨triangle_free_of_rank_le_two G hr.le, ?_⟩
      intro H _ hH
      rw [he]
      simpa only [Fintype.card_fin, turanNumber_two] using hH.card_edgeFinset_le
    obtain ⟨_, rfl, hf⟩ : ∃ k, k = n ∧ Nonempty (G ≃g turanGraph k 2) :=
      ⟨Fintype.card (Fin n), Fintype.card_fin n, hmax.nonempty_iso_turanGraph⟩
    exact hf
  · rintro ⟨hn4, ⟨f⟩⟩
    have hmat : ((turanGraph n 2).adjMatrix ℝ).submatrix f f = G.adjMatrix ℝ := by
      ext i j
      simp only [Matrix.submatrix_apply, SimpleGraph.adjMatrix_apply]
      exact if_congr f.map_rel_iff rfl rfl
    have hr : (G.adjMatrix ℝ).rank = 2 := le_antisymm
      (by rw [← hmat]; exact (Matrix.rank_submatrix_le _ _ _).trans (turan_rank_le_two n))
      (rank_ge_two G hn hc)
    have he : G.edgeFinset.card = n^2/4 := f.card_edgeFinset_eq.trans turanNumber_two
    rw [hr, he]
    interval_cases n <;> norm_num

#print axioms stronger
#print axioms conjecture_124806
#print axioms equality_iff

end TraceRanks
