module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2, Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2 =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.DblEval

theorem lintegral_partL_eq : ∀ {F : Type} [Field F] [NumberField F] {κ κ' : Type} [Fintype κ] [Fintype κ']
    (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)),
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖T φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ Φ ∈ schA F (κ ⊕ κ'), partL T Φ ∈ schA F (κ ⊕ κ')) →
    ∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ κ' _ _ T hT hmem μ hμ
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  letI mX : MeasurableSpace (κ → AF F) := borel _
  haveI : BorelSpace (κ → AF F) := ⟨rfl⟩
  letI mY : MeasurableSpace (κ' → AF F) := borel _
  haveI : BorelSpace (κ' → AF F) := ⟨rfl⟩
  letI mZ : MeasurableSpace (κ ⊕ κ' → AF F) := borel _
  haveI : BorelSpace (κ ⊕ κ' → AF F) := ⟨rfl⟩
  let μ₁ : Measure (κ → AF F) := Measure.addHaar
  let μ₂ : Measure (κ' → AF F) := Measure.addHaar
  obtain ⟨C₁, hC₁⟩ := hT μ₁ inferInstance
  refine ⟨C₁, fun Φ hΦ => ?_⟩
  let e : (κ ⊕ κ' → AF F) ≃ₜ (κ → AF F) × (κ' → AF F) := Homeomorph.sumArrowHomeomorphProdArrow
  let eA : ((κ → AF F) × (κ' → AF F)) ≃ₜ+ (κ ⊕ κ' → AF F) :=
    { e.symm with map_add' := fun a b => by funext i; cases i <;> rfl }
  let ν : Measure (κ ⊕ κ' → AF F) := (μ₁.prod μ₂).map eA
  haveI : ν.IsAddHaarMeasure := eA.isAddHaarMeasure_map _
  obtain ⟨c, hμν⟩ : ∃ c : ℝ≥0, μ = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul μ ν⟩
  have key : ∀ f : (κ ⊕ κ' → AF F) → ℝ≥0∞, Measurable f →
      ∫⁻ z, f z ∂μ = c * ∫⁻ y, ∫⁻ x, f (Sum.elim x y) ∂μ₁ ∂μ₂ := by
    intro f hf
    have hmeas : Measurable (⇑eA) := eA.continuous.measurable
    rw [hμν, lintegral_smul_measure]
    simp only [ν]
    rw [lintegral_map hf hmeas, lintegral_prod_symm (fun p => f (eA p)) (hf.comp hmeas).aemeasurable]
    rfl
  have hc1 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F (hmem Φ hΦ)
  have hc2 := GlobalTheory.ThetaTransformMeas.continuous_of_mem_schA F hΦ
  rw [key _ (hc1.measurable.enorm.pow_const 2), key _ (hc2.measurable.enorm.pow_const 2)]
  have inner : ∀ y, ∫⁻ x, ‖partL T Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ = C₁ * ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    fun y => hC₁ _ (sliceL_mem hΦ y)
  have hm : Measurable fun y => ∫⁻ x, ‖Φ (Sum.elim x y)‖ₑ ^ 2 ∂μ₁ :=
    Measurable.lintegral_prod_left' (f := fun p : (κ → AF F) × (κ' → AF F) => ‖Φ (eA p)‖ₑ ^ 2)
      ((hc2.comp eA.continuous).measurable.enorm.pow_const 2)
  simp_rw [inner]
  rw [lintegral_const_mul _ hm]
  ring

end GlobalTheory.DblEval

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2 =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinApply\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDblCoordDblD\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFourierPreservesSchwartzL2\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialRightPreservesL2Norm\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzConjMem\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLocalOperator\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts\n\n"}
section -- clump:auto
@[expose] public section

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partLe (U : ((κ → A) → ℂ) ≃ₗ[ℂ] ((κ₁ → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁ ⊕ κ' → A) → ℂ) :=
  { partLₗ U.toLinearMap with
    invFun := partL U.symm
    left_inv := fun Φ => by
      show partL U.symm (partL U Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.symm_apply_apply]
      exact partL_id Φ
    right_inv := fun Φ => by
      show partL U (partL U.symm Φ) = Φ
      rw [partL_partL]
      simp only [LinearEquiv.apply_symm_apply]
      exact partL_id Φ }

def partRe (U : ((κ' → A) → ℂ) ≃ₗ[ℂ] ((κ₁' → A) → ℂ)) : ((κ ⊕ κ' → A) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ₁' → A) → ℂ) :=
  { partRₗ U.toLinearMap with
    invFun := partR U.symm
    left_inv := fun Φ => by
      show partR U.symm (partR U Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.symm_apply_apply]
      exact partR_id Φ
    right_inv := fun Φ => by
      show partR U (partR U.symm Φ) = Φ
      rw [partR_partR]
      simp only [LinearEquiv.apply_symm_apply]
      exact partR_id Φ }

end Blocks

def conjE {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ) :=
  { conjLin U.toLinearMap with
    invFun := conjLin U.symm.toLinearMap
    left_inv := fun φ => by
      funext x
      simp [conjLin_apply]
    right_inv := fun φ => by
      funext x
      simp [conjLin_apply] }

theorem conjE_apply {X Y : Type} (U : (X → ℂ) ≃ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) : conjE U φ = conjLin U.toLinearMap φ := rfl

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Gen

variable {F : Type} [Field F] [NumberField F]

theorem partL_eq_of_eqOn {κ κ₁ κ' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ → AF F) → ℂ) → (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partL T Φ = partL e Φ :=
  partL_congr fun b => h _ (sliceL_mem hΦ b)

theorem partR_eq_of_eqOn {κ κ' κ₁' : Type} [Fintype κ] [Fintype κ'] {T e : ((κ' → AF F) → ℂ) → (κ₁' → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ', T Φ = e Φ) {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ')) :
    partR T Φ = partR e Φ :=
  partR_congr fun a => h _ (sliceR_mem hΦ a)

theorem conjLin_eq_of_eqOn {κ κ₁ : Type} [Fintype κ] {T e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ}
    (h : ∀ Φ ∈ schA F κ, T Φ = e Φ) : ∀ Φ ∈ schA F κ, conjLin T Φ = conjLin e Φ := fun Φ hΦ => by
  funext y
  rw [conjLin_apply, conjLin_apply, h _ (GlobalTheory.ConjSch.conj_mem_schA Φ hΦ)]

theorem adm_congr {κ : Type} [Fintype κ] {l l' : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ} (h : ∀ Φ ∈ schA F κ, l Φ = l' Φ)
    (hl : l' ∈ (adeleClass F).adm κ) : l ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨T, hT⟩ := hl g hg
  exact ⟨T, fun f => by rw [h _ (Submodule.subset_span ⟨f, g, hg, rfl⟩), hT]⟩

theorem dbl_eq {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partR (conjLin U.toLinearMap) (partL U Φ) = partR (conjLin u) (partL u Φ) ∧
      partR (conjLin u) (partL u Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partL U Φ = partL u Φ := partL_eq_of_eqOn hUu hΦ
  have h2 : partL u Φ ∈ schA F (κ ⊕ κ) := partL_mem u hu Φ hΦ
  refine ⟨?_, partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) _ h2⟩
  rw [h1]
  exact partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) h2

theorem dbl_eq' {κ : Type} [Fintype κ] (U : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ))
    (u : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) (hu : IsLocOp u) (hUu : ∀ Φ ∈ schA F κ, U Φ = u Φ)
    {Φ : (κ ⊕ κ → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ)) :
    partL U (partR (conjLin U.toLinearMap) Φ) = partL u (partR (conjLin u) Φ) ∧
      partL u (partR (conjLin u) Φ) ∈ schA F (κ ⊕ κ) := by
  have h1 : partR (conjLin U.toLinearMap) Φ = partR (conjLin u) Φ :=
    partR_eq_of_eqOn (conjLin_eq_of_eqOn (T := U.toLinearMap) hUu) hΦ
  have h2 : partR (conjLin u) Φ ∈ schA F (κ ⊕ κ) :=
    partR_mem (conjLin u) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin u hu) Φ hΦ
  refine ⟨?_, partL_mem u hu _ h2⟩
  rw [h1]
  exact partL_eq_of_eqOn hUu h2

end Gen

end GlobalTheory.DblTr

namespace GlobalTheory.DblTr

section Main

variable {F : Type} [Field F] [NumberField F]

theorem hasDbl_of_loc {E' : Type} [CommRing E'] [Algebra (AF F) E'] (c : E' →ₐ[AF F] E') {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E') (JA : Matrix α α E') (JB : Matrix β β E') {κ : Type}
    [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : ∀ t, ‖ψ t‖ = 1) (d d₁ : Darboux (symp c ξ JA JB) κ)
    (T : ((κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ → AF F) → ℂ)) (e e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ))
    (hL : IsLocOp e) (hL' : IsLocOp e') (hTe : ∀ Φ ∈ schA F κ, T Φ = e Φ)
    (hTe' : ∀ Φ ∈ schA F κ, T.symm Φ = e' Φ) (hmem : ∀ Φ, Φ ∈ schA F κ ↔ T Φ ∈ schA F κ)
    (Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F κ, T (d.rho ψ w Φ) = d₁.rho ψ w (T Φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) :
    HasDbl c (adeleClass F) ψ ξ JA JB d d₁ T := by
  intro dd hdd
  have hconj : ∀ Φ ∈ schA F κ, (fun x => starRingEnd ℂ (Φ x)) ∈ schA F κ := fun Φ hΦ =>
    GlobalTheory.ConjSch.conj_mem_schA Φ hΦ

  have hSmem : ∀ φ, φ ∈ schA F κ ↔ conjE T φ ∈ schA F κ := fun φ => by
    constructor
    · intro hφ
      have := hconj _ ((hmem _).1 (hconj φ hφ))
      exact this
    · intro hφ
      have h1 : (fun x => starRingEnd ℂ (conjE T φ x)) = T (fun x => starRingEnd ℂ (φ x)) := by
        funext x; simp [conjE_apply, conjLin_apply]
      have h2 := hconj _ hφ
      rw [h1, ← hmem] at h2
      have h3 := hconj _ h2
      simpa using h3

  have hLmem : ∀ Φ ∈ schA F (κ ⊕ κ), partL T Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    rw [partL_eq_of_eqOn hTe hΦ]; exact partL_mem e hL Φ hΦ
  have hRmem : ∀ Φ ∈ schA F (κ ⊕ κ), partR (conjE T) Φ ∈ schA F (κ ⊕ κ) := fun Φ hΦ => by
    have h := partR_eq_of_eqOn (κ := κ) (conjLin_eq_of_eqOn (T := T.toLinearMap) hTe) hΦ
    rw [show partR (conjE T) Φ = partR (conjLin T.toLinearMap) Φ from rfl, h]
    exact partR_mem (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) Φ hΦ

  have heis₂ : ∀ w, ∀ φ ∈ schA F κ, conjE T (d.rho ψ⁻¹ w φ) = d₁.rho ψ⁻¹ w (conjE T φ) := fun w φ hφ => by
    funext y
    rw [conjE_apply, conjLin_apply]
    have h1 : (fun x => starRingEnd ℂ (d.rho ψ⁻¹ w φ x)) = d.rho ψ w (fun x => starRingEnd ℂ (φ x)) :=
      funext fun x => conj_schr_inv ψ hψ _ _ _
    rw [LinearEquiv.coe_coe, h1, Heisenberg₂ w _ (hconj φ hφ)]
    exact conj_schr ψ hψ _ _ _

  have hunitS : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F κ, ∫⁻ x, ‖conjE T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := fun μ hμ => by
    obtain ⟨C, hC⟩ := hunit μ hμ
    refine ⟨C, fun Φ hΦ => ?_⟩
    have h1 := hC _ (hconj Φ hΦ)
    have hce : ∀ z : ℂ, ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := fun z => by
      rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
      congr 1
      ext
      simp
    simp only [conjE_apply, conjLin_apply, LinearEquiv.coe_coe, hce] at h1 ⊢
    exact h1
  set Td : ((κ ⊕ κ → AF F) → ℂ) ≃ₗ[ℂ] ((κ ⊕ κ → AF F) → ℂ) := (partLe (κ' := κ) T).trans (partRe (κ := κ) (conjE T))
    with hTd
  have hTd_apply : ∀ Φ, Td Φ = partR (conjE T) (partL T Φ) := fun Φ => rfl
  have hTd_symm : ∀ Φ, Td.symm Φ = partL T.symm (partR (conjE T).symm Φ) := fun Φ => rfl
  have hTeq : ∀ Φ ∈ schA F (κ ⊕ κ), Td Φ = partR (conjLin e) (partL e Φ) ∧ partR (conjLin e) (partL e Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq T e hL hTe hΦ
  have hTeq' : ∀ Φ ∈ schA F (κ ⊕ κ), Td.symm Φ = partL e' (partR (conjLin e') Φ) ∧
      partL e' (partR (conjLin e') Φ) ∈ schA F (κ ⊕ κ) :=
    fun Φ hΦ => dbl_eq' T.symm e' hL' hTe' hΦ
  refine ⟨GlobalTheory.DblSchr.dblD c d₁, Td, conjE T, GlobalTheory.DblSchr.isDblCoord_dblD c d₁, ⟨fun Φ => ?_, fun w Φ hΦ => ?_,
    fun l => ?_, fun μ hμ => ?_⟩, hSmem, fun φ₁ _ φ₂ _ => ?_⟩
  · constructor
    · intro hΦ
      rw [(hTeq Φ hΦ).1]; exact (hTeq Φ hΦ).2
    · intro hΦ
      have := (hTeq' _ hΦ)
      rw [LinearEquiv.symm_apply_apply] at this
      rw [this.1]; exact this.2
  · rw [← Matrix.fromCols_toCols w, rho_dbl c ξ JA JB d dd hdd, rho_dbl c ξ JA JB d₁ _ (GlobalTheory.DblSchr.isDblCoord_dblD c d₁),
      hTd_apply, hTd_apply]
    have hc1 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partL T (partR (d.rho ψ⁻¹ w.toCols₂) Ψ) =
        partR (d.rho ψ⁻¹ w.toCols₂) (partL T Ψ) := fun Ψ => partL_partR_rho T.toLinearMap d ψ⁻¹ _ Ψ
    have hc2 : ∀ Ψ : (κ ⊕ κ → AF F) → ℂ, partR (conjE T) (partL (d₁.rho ψ w.toCols₁) Ψ) =
        partL (d₁.rho ψ w.toCols₁) (partR (conjE T) Ψ) := fun Ψ => partR_partL_rho (conjE T).toLinearMap d₁ ψ _ Ψ
    rw [partL_intertwine T (d.rho ψ w.toCols₁) (d₁.rho ψ w.toCols₁) T _ (fun φ hφ => Heisenberg₂ _ φ hφ)
        (fun b => by rw [sliceL_partR_rho]; exact Submodule.smul_mem _ _ (sliceL_mem hΦ _)),
      hc1, hc2,
      partR_intertwine (conjE T) (d.rho ψ⁻¹ w.toCols₂) (d₁.rho ψ⁻¹ w.toCols₂) (conjE T) _ (fun φ hφ => heis₂ _ φ hφ)
        (fun a => sliceR_mem (hLmem Φ hΦ) a)]
  · constructor
    · intro hl
      refine adm_congr (l' := (l ∘ₗ partRₗ (conjLin e)) ∘ₗ partLₗ e) (fun Φ hΦ => ?_)
        (partL_adm e hL _ (partR_adm (conjLin e) (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e hL) l hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [(hTeq Φ hΦ).1]
    · intro hl
      refine adm_congr (l' := ((l ∘ₗ Td.toLinearMap) ∘ₗ partLₗ e') ∘ₗ partRₗ (conjLin e')) (fun Φ hΦ => ?_)
        (partR_adm (conjLin e') (GlobalTheory.DblEval.ConjLoc.isLocOp_conjLin e' hL') _ (partL_adm e' hL' _ hl))
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, partLₗ_apply, partRₗ_apply]
      rw [← (hTeq' Φ hΦ).1, LinearEquiv.apply_symm_apply]
  · obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.DblEval.lintegral_partL_eq T.toLinearMap hunit hLmem μ hμ
    obtain ⟨C₂, hC₂⟩ := _root_.GlobalTheory.DblEval.L2RightPartial.partR_lintegral_sq_eq_const_mul_of_mem_schA (κ := κ) (conjE T).toLinearMap hunitS hRmem μ hμ
    refine ⟨C₂ * C₁, fun φ hφ => ?_⟩
    rw [hTd_apply]
    have h2 := hC₂ _ (hLmem φ hφ)
    have h1 := hC₁ φ hφ
    simp only [LinearEquiv.coe_coe] at h1 h2
    rw [h2, h1, mul_assoc]
  · funext y
    rw [hTd_apply]
    simp only [partR, partL, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]
    have h1 : (fun x => T (fun x' => φ₁ x' * φ₂ x) (y ∘ Sum.inl)) = T φ₁ (y ∘ Sum.inl) • φ₂ := funext fun x => by
      rw [show (fun x' => φ₁ x' * φ₂ x) = φ₂ x • φ₁ from funext fun x' => by simp [mul_comm], map_smul]
      simp [mul_comm]
    rw [h1, map_smul]
    rfl

end Main

end GlobalTheory.DblTr
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn =====
