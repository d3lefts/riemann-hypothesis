module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

theorem logDeriv_eq_order_div_add_analytic :
    ∀ (f : ℂ → ℂ) (p : ℂ), AnalyticAt ℂ f p → (¬ ∀ᶠ s in 𝓝 p, f s = 0) →
      ∃ g : ℂ → ℂ, AnalyticAt ℂ g p ∧ ∀ᶠ s in 𝓝[≠] p, f s ≠ 0 ∧
        deriv f s / f s = ((analyticOrderNatAt f p : ℕ) : ℂ) / (s - p) + g s := by
  intro f p hf hne
  have htop : analyticOrderAt f p ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]; exact hne
  obtain ⟨g, hg, hg0, hfg⟩ := (hf.analyticOrderNatAt_eq_iff htop (n := analyticOrderNatAt f p)).mp rfl
  set m := analyticOrderNatAt f p with hm
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_⟩
  have h1 : ∀ᶠ s in 𝓝 p, g s ≠ 0 := hg.continuousAt.eventually_ne hg0
  have h2 : ∀ᶠ s in 𝓝 p, AnalyticAt ℂ g s := hg.eventually_analyticAt
  have h3 := hfg.eventually_nhds
  have h4 : ∀ᶠ s in 𝓝[≠] p, s ≠ p := self_mem_nhdsWithin
  filter_upwards [h4, nhdsWithin_le_nhds h1, nhdsWithin_le_nhds h2, nhdsWithin_le_nhds h3]
    with s hsp hs1 hs2 hs3
  have hsub : s - p ≠ 0 := sub_ne_zero.mpr hsp
  have hev : f =ᶠ[𝓝 s] fun z => (z - p) ^ m * g z := by
    filter_upwards [hs3] with z hz
    rw [hz, smul_eq_mul]
  have hfs : f s = (s - p) ^ m * g s := hev.eq_of_nhds
  refine ⟨by rw [hfs]; exact mul_ne_zero (pow_ne_zero _ hsub) hs1, ?_⟩
  change logDeriv f s = _
  rw [(logDeriv_congr_nhds hev).eq_of_nhds,
    logDeriv_fun_mul (f := fun z : ℂ => (z - p) ^ m) (g := g) s (pow_ne_zero _ hsub) hs1
      ((differentiableAt_id.sub_const p).pow m) hs2.differentiableAt,
    logDeriv_fun_pow (f := fun z : ℂ => z - p) (differentiableAt_id.sub_const p)]
  simp [logDeriv_apply, div_eq_mul_inv]

/-- Multiplying a simple principal part by a holomorphic weight multiplies its residue
by the value of that weight. The minus sign matches the explicit-formula convention. -/
theorem neg_mul_eq_residue_div_add_analytic
    {φ g W : ℂ → ℂ} {p k : ℂ}
    (hg : AnalyticAt ℂ g p) (hW : AnalyticAt ℂ W p)
    (hφ : ∀ᶠ s in 𝓝[≠] p, φ s = k / (s - p) + g s) :
    ∃ G : ℂ → ℂ, AnalyticAt ℂ G p ∧
      ∀ᶠ s in 𝓝[≠] p, -φ s * W s = -(k * W p) / (s - p) + G s := by
  refine ⟨fun s => -(k * dslope W p s) - g s * W s,
    ((analyticAt_const.mul (hW.dslope p)).neg).sub (hg.mul hW), ?_⟩
  filter_upwards [hφ, self_mem_nhdsWithin] with s hs hsp
  rw [hs, dslope_of_ne _ hsp, slope_def_field]
  field_simp [sub_ne_zero.mpr hsp]
  ring

end GlobalTheory
