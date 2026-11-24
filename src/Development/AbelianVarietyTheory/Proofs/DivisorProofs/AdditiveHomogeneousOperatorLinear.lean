module

import Development.WeilBound.ThetaLifts.FrameEstimates.FinBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.PlaneFormNondegenerate
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SchurLin

section General

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem sb_translate {f : V → ℂ} (hf : f ∈ SB V) (Z : V) : (fun Y => f (Y + Z)) ∈ SB V :=
  ⟨hf.1.comp_continuous (Homeomorph.addRight Z).continuous, hf.2.comp_homeomorph (Homeomorph.addRight Z)⟩

theorem sb_indicator (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V)) :
    (U : Set V).indicator (1 : V → ℂ) ∈ SB V := by
  have hcl : IsClosed (U : Set V) := AddSubgroup.isClosed_of_isOpen U ho
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ (U : Set V)
    · filter_upwards [ho.mem_nhds hx] with y hy
      simp [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isOpen_compl.mem_nhds hx] with y hy
      simp [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  exact HasCompactSupport.intro' hc hcl (fun x hx => Set.indicator_of_notMem hx _)

theorem sb_eventually_invariant {f : V → ℂ} (hf : f ∈ SB V) :
    ∀ᶠ w in 𝓝 (0 : V), ∀ Y, f (Y + w) = f Y := by
  apply PositivityTheory.ThKEst.W.sb_inv <;> assumption

variable (A : (V → ℂ) → V → ℂ)

theorem eq_smul_of_invariant
    (hadd : ∀ f ∈ SB V, ∀ f' ∈ SB V, A (f + f') = A f + A f')
    (hsmul : ∀ (c : ℂ), ∀ f ∈ SB V, A (c • f) = c • A f)
    (htr : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z))
    (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V)) (c : ℂ)
    (hA : A ((U : Set V).indicator 1) = c • (U : Set V).indicator 1)
    {f : V → ℂ} (hf : f ∈ SB V) (hinv : ∀ Y, ∀ u ∈ U, f (Y + u) = f Y) : A f = c • f := by
  classical
  set e : V → ℂ := (U : Set V).indicator 1 with he_def
  have he : e ∈ SB V := sb_indicator U ho hc
  haveI := QuotientAddGroup.discreteTopology ho
  have hfin : ((QuotientAddGroup.mk : V → V ⧸ U) '' tsupport f).Finite :=
    (hf.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set S := hfin.toFinset
  let g : V ⧸ U → V → ℂ := fun q Y => e (Y + -q.out)
  have hg : ∀ q, g q ∈ SB V := fun q => sb_translate he _
  have hAg : ∀ q, A (g q) = c • g q := by
    intro q
    show A (fun Y => e (Y + -q.out)) = _
    rw [htr _ _ he, hA]
    rfl
  have hgq : ∀ q Y, g q Y = if (QuotientAddGroup.mk Y : V ⧸ U) = q then 1 else 0 := by
    intro q Y
    have : (QuotientAddGroup.mk Y : V ⧸ U) = q ↔ Y + -q.out ∈ U := by
      conv_lhs => rw [← Quotient.out_eq' q]
      rw [eq_comm]
      show (QuotientAddGroup.mk q.out : V ⧸ U) = QuotientAddGroup.mk Y ↔ _
      rw [QuotientAddGroup.eq, show Y + -q.out = -q.out + Y by abel]
    simp only [g, e, Set.indicator_apply, SetLike.mem_coe, Pi.one_apply, this]
  have hdec : f = ∑ q ∈ S, f q.out • g q := by
    funext Y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hgq, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq]
    split_ifs with hS
    · have h1 : (QuotientAddGroup.mk (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) : V ⧸ U)
          = QuotientAddGroup.mk Y := Quotient.out_eq' _
      rw [QuotientAddGroup.eq] at h1
      have := hinv (Quotient.out (QuotientAddGroup.mk Y : V ⧸ U)) _ h1
      rw [add_neg_cancel_left] at this
      exact this
    · have : Y ∉ tsupport f := fun h => hS (hfin.mem_toFinset.2 ⟨Y, h, rfl⟩)
      exact image_eq_zero_of_notMem_tsupport this
  have hzero : A 0 = 0 := by
    have := hsmul 0 e he
    simpa using this
  have hsum : ∀ T : Finset (V ⧸ U),
      A (∑ q ∈ T, f q.out • g q) = ∑ q ∈ T, f q.out • A (g q) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simpa using hzero
    | insert a T ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hadd _ ((SB V).smul_mem _ (hg a)) _ ((SB V).sum_mem fun q _ => (SB V).smul_mem _ (hg q)),
        hsmul _ _ (hg a), ih]
  rw [hdec, hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hAg, smul_comm]

theorem indicator_eigen
    (htr : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => f (Y + Z)) = fun Y => A f (Y + Z))
    (χ : V → V → ℂ)
    (hmul : ∀ Z : V, ∀ f ∈ SB V, A (fun Y => χ Z Y * f Y) = fun Y => χ Z Y * A f Y)
    (U : AddSubgroup V) (ho : IsOpen (U : Set V)) (hc : IsCompact (U : Set V))
    (hsep : ∀ Y ∉ U, ∃ Z, χ Z Y ≠ 1 ∧ ∀ u ∈ U, χ Z u = 1) :
    A ((U : Set V).indicator 1) = A ((U : Set V).indicator 1) 0 • (U : Set V).indicator 1 := by
  classical
  set e : V → ℂ := (U : Set V).indicator 1 with he_def
  have he : e ∈ SB V := sb_indicator U ho hc
  have hinv : ∀ u ∈ U, ∀ Y, A e (Y + u) = A e Y := by
    intro u hu Y
    have : (fun Y => e (Y + u)) = e := by
      funext Y
      simp [e, Set.indicator_apply, U.add_mem_cancel_right hu]
    have h := htr u e he
    rw [this] at h
    exact (congrFun h Y).symm
  have hzero : ∀ Y ∉ U, A e Y = 0 := by
    intro Y hY
    obtain ⟨Z, hZY, hZU⟩ := hsep Y hY
    have : (fun Y => χ Z Y * e Y) = e := by
      funext Y
      by_cases h : Y ∈ U
      · simp [e, h, hZU Y h]
      · simp [e, h]
    have h := hmul Z e he
    rw [this] at h
    have h2 := congrFun h Y
    have h3 : (χ Z Y - 1) * A e Y = 0 := by linear_combination (-1 : ℂ) * h2
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h) hZY
    · exact h
  funext Y
  by_cases hY : Y ∈ U
  · have := hinv Y hY 0
    simp only [zero_add] at this
    simp [e, hY, this]
  · simp [e, hY, hzero Y hY]

end General

end GlobalTheory.SchurLin

namespace GlobalTheory.SchurLin

section Local

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

def dualBall (ψ : AddChar K ℂ) (t : K) : AddSubgroup K where
  carrier := {y | ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1}
  zero_mem' := by
    intro o _
    simp
  add_mem' := by
    intro a b ha hb o ho
    simp only [Set.mem_setOf_eq] at *
    rw [mul_add, mul_add, AddChar.map_add_eq_mul, ha o ho, hb o ho, one_mul]
  neg_mem' := by
    intro a ha o ho
    have h : ψ (o * (t * a)) = 1 := ha o ho
    have h2 : ψ (o * (t * -a)) * ψ (o * (t * a)) = 1 := by
      rw [← AddChar.map_add_eq_mul, show o * (t * -a) + o * (t * a) = 0 by ring,
        AddChar.map_zero_eq_one]
    rw [h, mul_one] at h2
    exact h2

theorem mem_dualBall {ψ : AddChar K ℂ} {t y : K} :
    y ∈ dualBall ψ t ↔ ∀ o ∈ (ValuativeRel.valuation K).integer, ψ (o * (t * y)) = 1 := Iff.rfl

theorem dualBall_mem_nhds {ψ : AddChar K ℂ} (hψc : Continuous ψ) (t : K) :
    (dualBall ψ t : Set K) ∈ 𝓝 0 := by
  have h := GlobalTheory.Published.SvN.eventually_psi hψc
  have ht : Tendsto (fun y : K => t * y) (𝓝 0) (𝓝 0) := by
    have := (continuous_const_mul t).tendsto (0 : K)
    rwa [mul_zero] at this
  filter_upwards [ht.eventually h] with y hy using hy

theorem dualBall_subset {ψ : AddChar K ℂ} {x₀ : K} (hx₀ : ψ x₀ ≠ 1) {t : K} (ht : t ≠ 0) :
    (dualBall ψ t : Set K) ⊆ {y | ValuativeRel.valuation K y ≤ ValuativeRel.valuation K (x₀ / t)} := by
  intro y hy
  by_contra hlt
  simp only [Set.mem_setOf_eq, not_le] at hlt
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hlt
  have ho : x₀ / t / y ∈ (ValuativeRel.valuation K).integer := by
    rw [Valuation.mem_integer_iff, map_div₀]
    exact div_le_one_of_le₀ hlt.le zero_le'
  have := hy _ ho
  rw [show x₀ / t / y * (t * y) = x₀ by field_simp] at this
  exact hx₀ this

variable (n m : ℕ)

def latt (ψ : AddChar K ℂ) (t : K) : AddSubgroup (Matrix (Fin n) (Fin m) K) where
  carrier := {Y | ∀ i j, Y i j ∈ dualBall ψ t}
  zero_mem' := fun _ _ => (dualBall ψ t).zero_mem
  add_mem' := fun ha hb i j => (dualBall ψ t).add_mem (ha i j) (hb i j)
  neg_mem' := fun ha i j => (dualBall ψ t).neg_mem (ha i j)

variable {n m}

theorem mem_latt {ψ : AddChar K ℂ} {t : K} {Y : Matrix (Fin n) (Fin m) K} :
    Y ∈ latt n m ψ t ↔ ∀ i j, Y i j ∈ dualBall ψ t := Iff.rfl

end Local

end GlobalTheory.SchurLin
