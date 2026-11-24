module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.WeilLinA

theorem omA_h_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (g : GL A k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β g 1 Φ = GlobalTheory.SplitFlip.omA ν 1 g 1 Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem omA_g_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type}
    [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ν β : kˣ →* ℂˣ) (h : GL D k) (Φ : Matrix A D k → ℂ) :
    GlobalTheory.SplitFlip.omA ν β 1 h Φ = GlobalTheory.SplitFlip.omA 1 β 1 h Φ := by
  funext X; simp [GlobalTheory.SplitFlip.omA]

theorem one_mem_UAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (Y : Spc F E n) {R : Type} [Zero R] (ev : AF F → R) : (1 : UA σ Y.J) ∈ UAt σ Y ev := by
  intro u _
  simp [mat]

theorem isSmoothChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsSmoothChar χ) : GlobalTheory.SmGL.IsSmoothChar χ⁻¹ := by
  have e : (χ⁻¹).ker = χ.ker := by ext x; simp [MonoidHom.mem_ker]
  unfold GlobalTheory.SmGL.IsSmoothChar at h ⊢
  rw [e]; exact h

theorem isUnitaryChar_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (χ : kˣ →* ℂˣ) (h : GlobalTheory.SmGL.IsUnitaryChar χ) : GlobalTheory.SmGL.IsUnitaryChar χ⁻¹ := by
  intro x
  have := h x
  simp [this]

end GlobalTheory.WeilLinA
