module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
open Filter Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem _root_.GlobalTheory.T.additive_homogeneous_operator_linear : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : AddChar K ℂ),
    Continuous ψ → ψ ≠ 1 → ∀ (n m : ℕ) (A : (Matrix (Fin n) (Fin m) K → ℂ) → Matrix (Fin n) (Fin m) K → ℂ),
    (∀ f ∈ SB (Matrix (Fin n) (Fin m) K), ∀ f' ∈ SB (Matrix (Fin n) (Fin m) K), A (f + f') = A f + A f') →
    (∀ (c : ℂ), ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A (c • f) = c • A f) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z)) →
    (∀ Z : Matrix (Fin n) (Fin m) K, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K),
      A (fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * f Y) = fun Y => ψ (∑ i, ∑ j, Y i j * Z i j) * A f Y) →
    ∃ c : ℂ, ∀ f ∈ SB (Matrix (Fin n) (Fin m) K), A f = c • f := by
  intro K _ _ _ _ ψ hψc hψ1 n m A hadd hsmul htr hmul
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : K, ψ x₀ ≠ 1 := by
    by_contra h
    push_neg at h
    apply hψ1
    ext x
    exact h x
  have hx00 : x₀ ≠ 0 := by
    rintro rfl
    exact hx₀ (AddChar.map_zero_eq_one ψ)
  let L : K → AddSubgroup (Matrix (Fin n) (Fin m) K) := fun t => GlobalTheory.SchurLin.latt n m ψ t
  have hLnhds : ∀ t, ((L t : AddSubgroup _) : Set (Matrix (Fin n) (Fin m) K)) ∈ 𝓝 0 := by
    intro t
    have h : ∀ i j, ∀ᶠ Y in 𝓝 (0 : Matrix (Fin n) (Fin m) K),
        Y i j ∈ GlobalTheory.SchurLin.dualBall ψ t :=
      fun i j => (((continuous_apply j).comp (continuous_apply i)).tendsto
        (0 : Matrix (Fin n) (Fin m) K)).eventually (GlobalTheory.SchurLin.dualBall_mem_nhds hψc t)
    filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 (h i)] with Y hY
      using hY
  have hLo : ∀ t, IsOpen ((L t : AddSubgroup _) : Set (Matrix (Fin n) (Fin m) K)) :=
    fun t => AddSubgroup.isOpen_of_mem_nhds (L t) (hLnhds t)
  have hLc : ∀ t, t ≠ 0 → IsCompact ((L t : AddSubgroup _) : Set (Matrix (Fin n) (Fin m) K)) := by
    intro t ht
    refine (isCompact_univ_pi (fun _ : Fin n => isCompact_univ_pi (fun _ : Fin m =>
      IsNonarchimedeanLocalField.isCompact_closedBall K
        (ValuativeRel.valuation K (x₀ / t))))).of_isClosed_subset
      (AddSubgroup.isClosed_of_isOpen (L t) (hLo t)) ?_
    intro Y hY i _ j _
    exact GlobalTheory.SchurLin.dualBall_subset hx₀ ht (hY i j)
  have hLsep : ∀ t, ∀ Y ∉ L t, ∃ Z : Matrix (Fin n) (Fin m) K,
      ψ (∑ i, ∑ j, Y i j * Z i j) ≠ 1 ∧ ∀ u ∈ L t, ψ (∑ i, ∑ j, u i j * Z i j) = 1 := by
    intro t Y hY
    simp only [L, GlobalTheory.SchurLin.mem_latt, GlobalTheory.SchurLin.mem_dualBall] at hY
    push_neg at hY
    obtain ⟨i, j, o, ho, hne⟩ := hY
    let Z : Matrix (Fin n) (Fin m) K := fun a b => if a = i ∧ b = j then o * t else 0
    have hsum : ∀ W : Matrix (Fin n) (Fin m) K,
        ∑ i', ∑ j', W i' j' * Z i' j' = o * (t * W i j) := by
      intro W
      rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
      · simp only [Z, and_self, if_true]
        ring
      · intro b _ hb
        simp [Z, hb]
      · simp
      · intro a _ ha
        simp [Z, ha]
      · simp
    refine ⟨Z, by rw [hsum]; exact hne, ?_⟩
    intro u hu
    rw [hsum]
    exact (GlobalTheory.SchurLin.mem_latt.1 hu i j) o ho
  -- small lattices
  have hsmall : ∀ W ∈ 𝓝 (0 : Matrix (Fin n) (Fin m) K), ∃ t : K, t ≠ 0 ∧
      ((L t : AddSubgroup _) : Set (Matrix (Fin n) (Fin m) K)) ⊆ W := by
    intro W hW
    set B : Set (Matrix (Fin n) (Fin m) K) :=
      Set.univ.pi fun _ => Set.univ.pi fun _ => {x : K | ValuativeRel.valuation K x ≤ 1}
    have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ =>
      IsNonarchimedeanLocalField.isCompact_closedBall K 1
    have h : ∀ᶠ s in 𝓝 (0 : K), ∀ Y ∈ B, s • Y ∈ W := by
      apply hB.eventually_forall_of_forall_eventually
      intro Y _
      have hc : Continuous (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2) :=
        continuous_fst.smul continuous_snd
      have h2 : Tendsto (fun z : K × Matrix (Fin n) (Fin m) K => z.1 • z.2)
          (𝓝 ((0 : K), Y)) (𝓝 0) := by
        convert hc.tendsto ((0 : K), Y) using 2
        simp
      exact h2.eventually hW
    obtain ⟨γ, hγ, hsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.1 h
    obtain ⟨r, hr0, hr1⟩ := Valuation.IsNontrivial.exists_lt_one (v := ValuativeRel.valuation K)
    obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective γ
    set s := r * a with hs
    have hvs : ValuativeRel.valuation K s < γ := by
      rw [hs, map_mul, ha]
      exact mul_lt_of_lt_one_left (zero_lt_iff.2 hγ) hr1
    have hs0 : s ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hvs
      have : ValuativeRel.valuation K r * γ = 0 := by
        rw [← ha, ← map_mul, ← hs, h0, map_zero]
      rcases mul_eq_zero.1 this with h | h
      · exact hr0 (by simpa using h)
      · exact hγ h
    refine ⟨x₀ / s, div_ne_zero hx00 hs0, ?_⟩
    intro Y hY
    have hxs : x₀ / (x₀ / s) = s := by field_simp
    have hYs : ∀ i j, ValuativeRel.valuation K (Y i j) ≤ ValuativeRel.valuation K s := by
      intro i j
      have := GlobalTheory.SchurLin.dualBall_subset hx₀ (div_ne_zero hx00 hs0) (hY i j)
      rwa [Set.mem_setOf_eq, hxs] at this
    have hmem : s⁻¹ • Y ∈ B := by
      intro i _ j _
      simp only [Set.mem_setOf_eq, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀]
      have hv0 : ValuativeRel.valuation K s ≠ 0 := by simpa using hs0
      rw [inv_mul_le_iff₀ (zero_lt_iff.2 hv0), mul_one]
      exact hYs i j
    have := hsub hvs (s⁻¹ • Y) hmem
    rwa [smul_smul, mul_inv_cancel₀ hs0, one_smul] at this
  -- fixed reference lattice
  have h10 : (1 : K) ≠ 0 := one_ne_zero
  set e₀ : Matrix (Fin n) (Fin m) K → ℂ := ((L 1 : AddSubgroup _) : Set _).indicator 1 with he₀
  have he₀sb : e₀ ∈ SB (Matrix (Fin n) (Fin m) K) :=
    GlobalTheory.SchurLin.sb_indicator (L 1) (hLo 1) (hLc 1 h10)
  refine ⟨A e₀ 0, fun f hf => ?_⟩
  have hfinv := GlobalTheory.SchurLin.sb_eventually_invariant hf
  obtain ⟨t, ht, htsub⟩ := hsmall _ (Filter.inter_mem hfinv (hLnhds 1))
  have heig := GlobalTheory.SchurLin.indicator_eigen A htr
    (fun Z Y => ψ (∑ i, ∑ j, Y i j * Z i j)) hmul (L t) (hLo t) (hLc t ht) (hLsep t)
  have key : ∀ g ∈ SB (Matrix (Fin n) (Fin m) K), (∀ Y, ∀ u ∈ L t, g (Y + u) = g Y) →
      A g = A (((L t : AddSubgroup _) : Set _).indicator 1) 0 • g :=
    fun g hg hgi => GlobalTheory.SchurLin.eq_smul_of_invariant A hadd hsmul htr (L t) (hLo t)
      (hLc t ht) _ heig hg hgi
  have hf' := key f hf (fun Y u hu => (htsub hu).1 Y)
  have he' := key e₀ he₀sb (fun Y u hu => by
    have hu1 : u ∈ L 1 := (htsub hu).2
    simp only [he₀, Set.indicator_apply, SetLike.mem_coe, (L 1).add_mem_cancel_right hu1, Pi.one_apply])
  have hc : A e₀ 0 = A (((L t : AddSubgroup _) : Set _).indicator 1) 0 := by
    rw [he', Pi.smul_apply, smul_eq_mul]
    simp [he₀, (L 1).zero_mem]
  rw [hc]
  exact hf'
