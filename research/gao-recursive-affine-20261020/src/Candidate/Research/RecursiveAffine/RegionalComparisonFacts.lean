/- Copyright (c) 2026 Hailey Collet; modifications (c) 2026 Zhongpai Gao.
Released under Apache 2.0. -/
import Candidate.Research.RecursiveAffine.RegionalLedger
set_option autoImplicit false
namespace OAI.SevenEighths.Cycle153Comparison
noncomputable section
variable [Cycle63.AffineLedger] in
/-- The plain lengths and the slots of a window of the ledger, whose overshoot over the unit with the slots priced at
`slotPrice` is at most `9/1000`, satisfy the facts that the old moment needs for the comparison of the ledger at the
width one, with the margin `9/1000` and the slack `1/1000`. -/
theorem regional_comparison_old_facts {x₁ x₂ z : ℝ} (hz : 0≤z)
    (hwin : Cycle63.AffineLedger.PlainWindow x₁ x₂ z)
    (hover : x₁+x₂+6*Cycle63.Optimization.slotPrice*z≤1+9/1000) :
    let Lc:=Cycle63.AffineLedger.comparisonLength x₁ x₂ z
    0<x₁ ∧ 0<x₂ ∧ x₁+x₂≤1 ∧ 0≤Lc ∧ Lc≤1/4 ∧ 0≤x₁+x₂-Lc ∧
      Lc+(x₁+x₂-Lc)+6*Cycle63.Optimization.slotPrice*z≤1+9/1000 ∧
      max 0 (1-(x₁+x₂-Lc)+1/1000)+Lc+6*Cycle63.Optimization.slotPrice*z+9/1000≤1 := by
  intro Lc
  have hvol:=hwin.volume_le hz
  have h1:=Cycle63.AffineLedger.comparisonLength_nonneg x₁ x₂ z hwin
  have h2:=Cycle63.AffineLedger.comparisonLength_le x₁ x₂ z hwin
  have h3:=Cycle63.AffineLedger.long_factor x₁ x₂ z hwin
  have h4:=Cycle63.AffineLedger.daughter_fits x₁ x₂ z hwin
  have hb:=Cycle63.AffineLedger.windowBottom_pos
  have hκ:=Cycle63.Optimization.slotPrice_mem
  have hκz : 6*Cycle63.Optimization.slotPrice*z≤(9/2)*z := by nlinarith [hκ.2]
  refine ⟨lt_of_lt_of_le hb hwin.left_ge,lt_of_lt_of_le hb hwin.right_ge,by linarith,h1,h2,by linarith,
    by linarith,?_⟩
  rcases le_total 0 (1-(x₁+x₂-Lc)+1/1000) with h|h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    linarith

end
end OAI.SevenEighths.Cycle153Comparison
#print axioms OAI.SevenEighths.Cycle153Comparison.regional_comparison_old_facts
